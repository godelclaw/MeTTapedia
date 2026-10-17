import Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
import MettaHyperonFull.Core.Atom
import Mathlib.Tactic.Tauto

/-!
# Binding models and solution theory of independent HE matching

The model carrier uses a structural encoding into `Metta.Atom`. Only its
syntax is imported: no matcher or evaluator correctness is an authority for
these judgments. A match presents its input equation and a merge presents
the conjunction of its input binding theories. Runtime comparisons consume
these laws downstream.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Translate HE grounded payloads into LeaTTa grounded payloads.

`custom` payloads are mapped into LeaTTa's `external` lane. This is a structural
embedding only; no claim is made yet that the host-side operational semantics of
custom/external payloads coincide. -/
def toLeaTTaGround : GroundedValue → Metta.Ground
  | .int n => .int n
  | .string s => .str s
  | .bool b => .bool b
  | .custom typeName payload => .external typeName payload

mutual

/-- Structural HE-atom translation into LeaTTa atoms. -/
def toLeaTTaAtom : Atom → Metta.Atom
  | .symbol s => .sym s
  | .var v => .var v
  | .grounded g => .gnd (toLeaTTaGround g)
  | .expression es => .expr (toLeaTTaAtoms es)

/-- Structural translation on atom lists. -/
def toLeaTTaAtoms : List Atom → List Metta.Atom
  | [] => []
  | a :: as => toLeaTTaAtom a :: toLeaTTaAtoms as

end

@[simp] theorem toLeaTTaAtoms_nil :
    toLeaTTaAtoms [] = [] := rfl

@[simp] theorem toLeaTTaAtoms_cons (a : Atom) (as : List Atom) :
    toLeaTTaAtoms (a :: as) = toLeaTTaAtom a :: toLeaTTaAtoms as := rfl

/-- Structural variable disjointness for query/rule matching, independent of
the fuel-bounded HE variable collector. -/
def VarsDisjoint (left right : Atom) : Prop :=
  ∀ v, v ∈ (toLeaTTaAtom left).vars →
    v ∉ (toLeaTTaAtom right).vars

/-- Structural variable disjointness is symmetric. -/
theorem VarsDisjoint.symm {left right : Atom}
    (h : VarsDisjoint left right) : VarsDisjoint right left := by
  intro v hright hleft
  exact h v hleft hright

/-- HE assignment-key uniqueness, stated explicitly so bridge lemmas can use it
without reaching into private helper files. -/
def AssignmentsNodup (b : Bindings) : Prop :=
  (b.assignments.map Prod.fst).Nodup

/-- Apply an extensional class-solution map throughout an atom.  This is the
fuel-independent semantic substitution layer shared by both engines. -/
def applyClassSolution
    (solution : String → Metta.Atom) : Metta.Atom → Metta.Atom
  | .sym s => .sym s
  | .var v => solution v
  | .gnd g => .gnd g
  | .expr atoms => .expr (atoms.map (applyClassSolution solution))

/-- A valuation satisfies the value and equality equations presented by one HE
binding record.  `applyClassSolution` is the homomorphic extension of the
valuation to atoms. -/
def HEBindingSatisfied
    (valuation : String → Metta.Atom) (b : Bindings) : Prop :=
  (∀ x value, (x, value) ∈ b.assignments →
      valuation x =
        applyClassSolution valuation (toLeaTTaAtom value)) ∧
  (∀ x y, (x, y) ∈ b.equalities → valuation x = valuation y)

/-- Extensional valuation equation presented by matching two HE atoms. -/
def HEAtomEquationSatisfied
    (valuation : String → Metta.Atom) (left right : Atom) : Prop :=
  applyClassSolution valuation (toLeaTTaAtom left) =
    applyClassSolution valuation (toLeaTTaAtom right)

/-- Pointwise equation theory for HE's list matcher. Length mismatch is
unsatisfiable, matching the executable failure branch. -/
def HEAtomListEquationsSatisfied
    (valuation : String → Metta.Atom) : List Atom → List Atom → Prop
  | [], [] => True
  | left :: lefts, right :: rights =>
      HEAtomEquationSatisfied valuation left right ∧
        HEAtomListEquationsSatisfied valuation lefts rights
  | _, _ => False


/-! ## Satisfaction: structural helpers -/

/-- The empty binding record constrains nothing. -/
theorem hesat_empty (μ : String → Metta.Atom) :
    HEBindingSatisfied μ Bindings.empty :=
  ⟨fun _ _ h => by simp [Bindings.empty] at h,
   fun _ _ h => by simp [Bindings.empty] at h⟩

@[simp] theorem hesat_empty_iff (μ : String → Metta.Atom) :
    HEBindingSatisfied μ Bindings.empty ↔ True :=
  iff_true_intro (hesat_empty μ)

private theorem eq_of_walk {μ : String → Metta.Atom} {b : Bindings}
    (hsat : ∀ x y, (x, y) ∈ b.equalities → μ x = μ y) :
    ∀ {x y : String},
      (EqualityClosure.edgeGraph b.equalities).Walk x y → μ x = μ y
  | _, _, .nil => rfl
  | _, _, .cons hadj tail => by
      rcases (EqualityClosure.edgeGraph_adj_iff.mp hadj).2 with hedge | hedge
      · exact (hsat _ _ hedge).trans (eq_of_walk hsat tail)
      · exact (hsat _ _ hedge).symm.trans (eq_of_walk hsat tail)

/-- A satisfying valuation is constant on every explicit equality class. -/
theorem HEBindingSatisfied.eq_of_mem_eqClass {μ : String → Metta.Atom}
    {b : Bindings} (hsat : HEBindingSatisfied μ b) {v w : String}
    (hmem : w ∈ b.eqClass v) : μ v = μ w :=
  (EqualityClosure.mem_eqClass_iff_reachable.mp hmem).elim
    fun walk => eq_of_walk hsat.2 walk

private theorem mem_of_lookup_eq_some {k : String} {a : Atom} :
    ∀ {l : List (String × Atom)}, l.lookup k = some a → (k, a) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k', a') :: l, h => by
      rw [List.lookup] at h
      cases hk : (k == k') with
      | false =>
          rw [hk] at h
          exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)
      | true =>
          rw [hk] at h
          have hkk : k = k' := eq_of_beq hk
          have haa : a' = a := Option.some.inj h
          subst hkk
          subst haa
          exact List.mem_cons_self ..

/-- A satisfying valuation sends a variable to (the solution image of) every
value carried anywhere in its equality class. -/
theorem HEBindingSatisfied.eq_applyClassSolution_of_mem_classValues
    {μ : String → Metta.Atom} {b : Bindings}
    (hsat : HEBindingSatisfied μ b) {v : String} {value : Atom}
    (hmem : value ∈ b.classValues v) :
    μ v = applyClassSolution μ (toLeaTTaAtom value) := by
  unfold Bindings.classValues at hmem
  rcases List.mem_filterMap.mp hmem with ⟨w, hw, hlookup⟩
  have hclass : w ∈ b.eqClass v :=
    EqualityClosure.mem_eqClassOrdered_iff.mp hw
  have hassign : (w, value) ∈ b.assignments :=
    mem_of_lookup_eq_some hlookup
  exact (hsat.eq_of_mem_eqClass hclass).trans (hsat.1 w value hassign)

theorem hesat_assign_of_not_isBound {b : Bindings} {v : String}
    {val : Atom} (hnb : b.isBound v = false) (μ : String → Metta.Atom) :
    HEBindingSatisfied μ (b.assign v val) ↔
      (HEBindingSatisfied μ b ∧
        μ v = applyClassSolution μ (toLeaTTaAtom val)) := by
  have hassign : b.assign v val =
      ⟨b.assignments ++ [(v, val)], b.equalities⟩ := by
    simp [Bindings.assign, hnb]
  rw [hassign]
  constructor
  · intro hsat
    exact ⟨⟨fun x value hx => hsat.1 x value (List.mem_append_left _ hx),
        hsat.2⟩,
      hsat.1 v val (List.mem_append_right _ (by simp))⟩
  · rintro ⟨hsat, hval⟩
    refine ⟨fun x value hx => ?_, hsat.2⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hsat.1 x value hx
    · simp only [List.mem_singleton, Prod.mk.injEq] at hx
      rcases hx with ⟨rfl, rfl⟩
      exact hval

theorem hesat_addEquality {b : Bindings} {a c : String}
    (μ : String → Metta.Atom) :
    HEBindingSatisfied μ (b.addEquality a c) ↔
      (HEBindingSatisfied μ b ∧ μ a = μ c) := by
  have heq : b.addEquality a c =
      ⟨b.assignments, b.equalities ++ [(a, c)]⟩ := rfl
  rw [heq]
  constructor
  · intro hsat
    exact ⟨⟨hsat.1, fun x y hx => hsat.2 x y (List.mem_append_left _ hx)⟩,
      hsat.2 a c (List.mem_append_right _ (by simp))⟩
  · rintro ⟨hsat, hac⟩
    refine ⟨hsat.1, fun x y hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hsat.2 x y hx
    · simp only [List.mem_singleton, Prod.mk.injEq] at hx
      rcases hx with ⟨rfl, rfl⟩
      exact hac

/-! ## The translated equation, by constructor -/

@[simp] theorem applyToLea_symbol (μ : String → Metta.Atom)
    (s : String) :
    applyClassSolution μ (toLeaTTaAtom (.symbol s)) = .sym s := by
  simp [toLeaTTaAtom, applyClassSolution]

@[simp] theorem applyToLea_var (μ : String → Metta.Atom)
    (v : String) :
    applyClassSolution μ (toLeaTTaAtom (.var v)) = μ v := by
  simp [toLeaTTaAtom, applyClassSolution]

@[simp] theorem applyToLea_grounded (μ : String → Metta.Atom)
    (g : GroundedValue) :
    applyClassSolution μ (toLeaTTaAtom (.grounded g)) =
      .gnd (toLeaTTaGround g) := by
  simp [toLeaTTaAtom, applyClassSolution]

@[simp] theorem applyToLea_expression (μ : String → Metta.Atom)
    (es : List Atom) :
    applyClassSolution μ (toLeaTTaAtom (.expression es)) =
      .expr ((toLeaTTaAtoms es).map (applyClassSolution μ)) := by
  simp [toLeaTTaAtom, applyClassSolution]

theorem solutionTheory_toLeaTTaAtoms_eq_map (l : List Atom) :
    toLeaTTaAtoms l = l.map toLeaTTaAtom := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem toLeaTTaAtoms_replicate (k : Nat) (a : Atom) :
    toLeaTTaAtoms (List.replicate k a) =
      List.replicate k (toLeaTTaAtom a) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- A constant list agrees with a mapped list exactly when every image is the
constant.  This is the solution reading of the class-wide reconciliation
worklists built by `addVarBinding`/`addVarEquality`. -/
theorem replicate_eq_map_iff (μ : String → Metta.Atom) (k : Atom) :
    ∀ l : List Atom,
      (List.replicate l.length (applyClassSolution μ (toLeaTTaAtom k)) =
        List.map (applyClassSolution μ ∘ toLeaTTaAtom) l) ↔
      ∀ o ∈ l, applyClassSolution μ (toLeaTTaAtom o) =
        applyClassSolution μ (toLeaTTaAtom k)
  | [] => by simp
  | o :: l => by
      simp only [List.length_cons, List.replicate_succ, List.map_cons,
        List.cons.injEq, List.forall_mem_cons, Function.comp]
      rw [replicate_eq_map_iff μ k l]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, h2⟩

/-- Under any valuation, a variable's image is no larger than the image of an
atom in which the variable occurs.  This is a general fact about the shared
homomorphic semantic substitution, independent of any unification engine. -/
theorem size_applyClassSolution_ge_of_mem_vars
    (valuation : String → Metta.Atom) (name : String) :
    ∀ atom : Metta.Atom, name ∈ atom.vars →
      (valuation name).size ≤
        (applyClassSolution valuation atom).size := by
  intro atom
  cases atom with
  | sym symbol =>
      intro hmem
      simp [Metta.Atom.vars] at hmem
  | var varName =>
      intro hmem
      simp only [Metta.Atom.vars, List.mem_singleton] at hmem
      subst varName
      simp [applyClassSolution]
  | gnd grounded =>
      intro hmem
      simp [Metta.Atom.vars] at hmem
  | expr atoms =>
      intro hmem
      simp only [Metta.Atom.vars, List.mem_flatten,
        List.mem_map] at hmem
      obtain ⟨varsList, ⟨child, hchild, rfl⟩, hname⟩ := hmem
      have hle := size_applyClassSolution_ge_of_mem_vars valuation name child hname
      have hmember :
          (applyClassSolution valuation child).size ∈
            ((atoms.map (applyClassSolution valuation)).map
              Metta.Atom.size) := by
        exact List.mem_map.mpr
          ⟨applyClassSolution valuation child,
            List.mem_map.mpr ⟨child, hchild, rfl⟩, rfl⟩
      have hsum :
          (applyClassSolution valuation child).size ≤
            ((atoms.map (applyClassSolution valuation)).map
              Metta.Atom.size).sum :=
        List.single_le_sum (by intro _ _; omega) _ hmember
      simp only [applyClassSolution, Metta.Atom.size]
      omega
termination_by atom => atom.size
decreasing_by
  simp only [Metta.Atom.size]
  have child_le : child.size ≤ (atoms.map Metta.Atom.size).sum :=
    List.single_le_sum (by intro _ _; exact Nat.zero_le _) _
      (List.mem_map_of_mem hchild)
  omega

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

namespace Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Satisfaction of one neutral spec binding constraint. -/
def ConstraintSatisfied
    (valuation : String → Metta.Atom) : Spec.Match.Merge.Constraint → Prop
  | .value varName value =>
      valuation varName =
        applyClassSolution valuation (toLeaTTaAtom value)
  | .equality left right => valuation left = valuation right

/-- Satisfaction of every constraint in a concrete fold ordering. -/
def ConstraintsSatisfied
    (valuation : String → Metta.Atom)
    (constraints : List Spec.Match.Merge.Constraint) : Prop :=
  ∀ constraint ∈ constraints, ConstraintSatisfied valuation constraint

@[simp] theorem value_mem_constraints_iff
    {bindings : Bindings} {varName : String} {value : Atom} :
    Spec.Match.Merge.Constraint.value varName value ∈
        Spec.Match.Merge.constraints bindings ↔
      (varName, value) ∈ bindings.assignments := by
  simp [Spec.Match.Merge.constraints]

@[simp] theorem equality_mem_constraints_iff
    {bindings : Bindings} {left right : String} :
    Spec.Match.Merge.Constraint.equality left right ∈
        Spec.Match.Merge.constraints bindings ↔
      (left, right) ∈ bindings.equalities := by
  simp [Spec.Match.Merge.constraints]

/-- The neutral constraint view presents exactly `HEBindingSatisfied`. -/
theorem constraintsSatisfied_constraints_iff
    (valuation : String → Metta.Atom) (bindings : Bindings) :
    ConstraintsSatisfied valuation
        (Spec.Match.Merge.constraints bindings) ↔
      HEBindingSatisfied valuation bindings := by
  constructor
  · intro hall
    refine ⟨?_, ?_⟩
    · intro varName value hmem
      exact hall (.value varName value)
        (value_mem_constraints_iff.mpr hmem)
    · intro left right hmem
      exact hall (.equality left right)
        (equality_mem_constraints_iff.mpr hmem)
  · rintro ⟨hvalues, hequalities⟩ constraint hmem
    cases constraint with
    | value varName value =>
        exact hvalues varName value
          (value_mem_constraints_iff.mp hmem)
    | equality left right =>
        exact hequalities left right
          (equality_mem_constraints_iff.mp hmem)

theorem constraintsSatisfied_iff_of_perm
    {valuation : String → Metta.Atom}
    {left right : List Spec.Match.Merge.Constraint}
    (hperm : left.Perm right) :
    ConstraintsSatisfied valuation left ↔
      ConstraintsSatisfied valuation right := by
  constructor
  · intro hall constraint hmem
    exact hall constraint ((List.Perm.mem_iff hperm).mpr hmem)
  · intro hall constraint hmem
    exact hall constraint ((List.Perm.mem_iff hperm).mp hmem)

/-! ## Simultaneous observation theorem -/

/-- The full six-relation mutual induction.  The public corollaries below
project its matcher and merge legs. -/
private theorem solutionPack
    {left right : Atom} {bindings : Bindings}
    (derivation : Spec.Match.Merge.MatchRel
      Spec.Match.Merge.equalityGroundedSemantic
      left right bindings) :
    ∀ valuation : String → Metta.Atom,
      (HEBindingSatisfied valuation bindings ↔
        applyClassSolution valuation (toLeaTTaAtom left) =
          applyClassSolution valuation (toLeaTTaAtom right)) := by
  apply Spec.Match.Merge.MatchRel.rec
    (motive_1 := fun left right bindings _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation bindings ↔
          applyClassSolution valuation (toLeaTTaAtom left) =
            applyClassSolution valuation (toLeaTTaAtom right)))
    (motive_2 := fun left right seed out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            (toLeaTTaAtoms left).map (applyClassSolution valuation) =
              (toLeaTTaAtoms right).map
                (applyClassSolution valuation)))
    (motive_3 := fun bindings varName value out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation bindings ∧
            valuation varName =
              applyClassSolution valuation (toLeaTTaAtom value)))
    (motive_4 := fun bindings left right out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation bindings ∧
            valuation left = valuation right))
    (motive_5 := fun seed constraints out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            ConstraintsSatisfied valuation constraints))
    (motive_6 := fun left right out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation left ∧
            HEBindingSatisfied valuation right))
    (t := derivation)
  next =>
      intro symbol hadmissible valuation
      simp
  next =>
      intro left right hadmissible valuation
      rw [hesat_addEquality]
      simp
  next =>
      intro varName value hnonvar hadmissible valuation
      rw [hesat_assign_of_not_isBound (by
        simp [Bindings.isBound, Bindings.lookup, Bindings.empty])]
      simp
  next =>
      intro value varName hnonvar hadmissible valuation
      rw [hesat_assign_of_not_isBound (by
        simp [Bindings.isBound, Bindings.lookup, Bindings.empty])]
      simp [eq_comm]
  next =>
      intro left right out hitems hadmissible ih valuation
      rw [ih valuation]
      simp [applyToLea_expression]
  next =>
      intro grounded right out hright hcustom hmatch hadmissible
      rcases hmatch with ⟨hrightEq, hout⟩
      subst right
      subst out
      intro valuation
      simp
  next =>
      intro left grounded out hleft hleftNoCustom hcustom hmatch hadmissible
      rcases hmatch with ⟨hleftEq, hout⟩
      subst left
      subst out
      intro valuation
      simp
  next =>
      intro left right hleft hright hadmissible
      exact (hleft (by
        simp [Spec.Match.Merge.equalityGroundedSemantic])).elim
  next =>
      intro seed valuation
      simp
  next =>
      intro left right lefts rights seed matched next out
        hmatch hmerge htail ihMatch ihMerge ihTail valuation
      rw [ihTail valuation, ihMerge valuation, ihMatch valuation]
      simp only [toLeaTTaAtoms_cons, List.map_cons, List.cons.injEq]
      tauto
  next =>
      intro bindings varName value hvalues valuation
      exact hesat_assign_of_not_isBound
        (isBound_eq_false_of_classValues_nil hvalues) valuation
  next =>
      intro bindings varName value first rest hvalues hagree hvalue
      subst value
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      constructor
      · intro hsat
        exact ⟨hsat,
          hsat.eq_applyClassSolution_of_mem_classValues hfirst⟩
      · exact fun hsat => hsat.1
  next =>
      intro bindings varName value first rest matched out hvalues hagree
        hne hmatch hmerge ihMatch ihMerge
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihMatch valuation]
      have hvalue : HEBindingSatisfied valuation bindings →
          valuation varName =
            applyClassSolution valuation (toLeaTTaAtom first) :=
        fun hsat =>
          hsat.eq_applyClassSolution_of_mem_classValues hfirst
      constructor
      · rintro ⟨hsat, hmatched⟩
        exact ⟨hsat, (hvalue hsat).trans hmatched⟩
      · rintro ⟨hsat, hnew⟩
        exact ⟨hsat, (hvalue hsat).symm.trans hnew⟩
  next =>
      intro bindings varName value first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihList valuation]
      simp only [hesat_empty_iff, true_and,
        solutionTheory_toLeaTTaAtoms_eq_map, List.map_map,
        List.map_replicate]
      rw [show rest.length + 1 = (rest ++ [value]).length by simp]
      rw [replicate_eq_map_iff valuation first (rest ++ [value])]
      have hhead : HEBindingSatisfied valuation bindings →
          valuation varName =
            applyClassSolution valuation (toLeaTTaAtom first) :=
        fun hsat =>
          hsat.eq_applyClassSolution_of_mem_classValues hfirst
      have hrest : HEBindingSatisfied valuation bindings →
          ∀ atom ∈ rest,
            applyClassSolution valuation (toLeaTTaAtom atom) =
              applyClassSolution valuation (toLeaTTaAtom first) := by
        intro hsat atom hatom
        have hclass : atom ∈ bindings.classValues varName :=
          (List.Perm.mem_iff hvalues).mp (by simp [hatom])
        exact
          (hsat.eq_applyClassSolution_of_mem_classValues hclass).symm.trans
            (hhead hsat)
      constructor
      · rintro ⟨hsat, hall⟩
        have hnew := hall value (List.mem_append_right rest (by simp))
        exact ⟨hsat, (hhead hsat).trans hnew.symm⟩
      · rintro ⟨hsat, hnew⟩
        refine ⟨hsat, fun atom hatom => ?_⟩
        rcases List.mem_append.mp hatom with hatom | hatom
        · exact hrest hsat atom hatom
        · simp only [List.mem_singleton] at hatom
          subst atom
          exact ((hhead hsat).symm.trans hnew).symm
  next =>
      intro bindings left right values hvalues hagree valuation
      exact hesat_addEquality valuation
  next =>
      intro bindings left right first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      have hfirst : first ∈
          (bindings.addEquality left right).classValues left :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihList valuation, hesat_addEquality]
      simp only [hesat_empty_iff, true_and,
        solutionTheory_toLeaTTaAtoms_eq_map, List.map_map,
        List.map_replicate]
      rw [replicate_eq_map_iff valuation first rest]
      have hall : HEBindingSatisfied valuation
            (bindings.addEquality left right) →
          ∀ atom ∈ rest,
            applyClassSolution valuation (toLeaTTaAtom atom) =
              applyClassSolution valuation (toLeaTTaAtom first) := by
        intro hsat atom hatom
        have hheadSat :=
          hsat.eq_applyClassSolution_of_mem_classValues hfirst
        have hclass : atom ∈
            (bindings.addEquality left right).classValues left :=
          (List.Perm.mem_iff hvalues).mp (by simp [hatom])
        exact
          (hsat.eq_applyClassSolution_of_mem_classValues hclass).symm.trans
            hheadSat
      constructor
      · rintro ⟨hsat, hallMatched⟩
        exact hsat
      · intro hsat
        have hcandidate := (hesat_addEquality valuation).mpr hsat
        exact ⟨hsat, hall hcandidate⟩
  next =>
      intro seed valuation
      simp [ConstraintsSatisfied]
  next =>
      intro seed next out varName value rest hadd htail ihAdd ihTail valuation
      rw [ihTail valuation, ihAdd valuation]
      simp [ConstraintsSatisfied, ConstraintSatisfied, and_assoc]
  next =>
      intro seed next out left right rest hadd htail ihAdd ihTail valuation
      rw [ihTail valuation, ihAdd valuation]
      simp [ConstraintsSatisfied, ConstraintSatisfied, and_assoc]
  next =>
      intro left right out order hperm hfold ihFold valuation
      rw [ihFold valuation,
        constraintsSatisfied_iff_of_perm hperm,
        constraintsSatisfied_constraints_iff]

/-- specification matching presents exactly the equation between its input atoms. -/
theorem matchRel_solution_iff
    {left right : Atom} {bindings : Bindings}
    (derivation : Spec.Match.Merge.MatchRel
      Spec.Match.Merge.equalityGroundedSemantic
      left right bindings)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation bindings ↔
      applyClassSolution valuation (toLeaTTaAtom left) =
        applyClassSolution valuation (toLeaTTaAtom right) :=
  solutionPack derivation valuation

/-- specification merging presents exactly the conjunction of its two input binding
theories.  This is the standalone merge-root projection of the same mutual
observation invariant used by `matchRel_solution_iff`. -/
theorem mergeRel_solution_iff
    {left right out : Bindings}
    (derivation : Spec.Match.Merge.MergeRel
      Spec.Match.Merge.equalityGroundedSemantic left right out)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation out ↔
      HEBindingSatisfied valuation left ∧
        HEBindingSatisfied valuation right := by
  apply Spec.Match.Merge.MergeRel.rec
    (motive_1 := fun left right bindings _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation bindings ↔
          applyClassSolution valuation (toLeaTTaAtom left) =
            applyClassSolution valuation (toLeaTTaAtom right)))
    (motive_2 := fun left right seed out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            (toLeaTTaAtoms left).map (applyClassSolution valuation) =
              (toLeaTTaAtoms right).map
                (applyClassSolution valuation)))
    (motive_3 := fun bindings varName value out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation bindings ∧
            valuation varName =
              applyClassSolution valuation (toLeaTTaAtom value)))
    (motive_4 := fun bindings left right out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation bindings ∧
            valuation left = valuation right))
    (motive_5 := fun seed constraints out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            ConstraintsSatisfied valuation constraints))
    (motive_6 := fun left right out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation left ∧
            HEBindingSatisfied valuation right))
    (t := derivation)
  next =>
      intro symbol hadmissible
      exact matchRel_solution_iff (.symSym symbol hadmissible)
  next =>
      intro left right hadmissible
      exact matchRel_solution_iff (.varVar left right hadmissible)
  next =>
      intro varName value hnonvar hadmissible
      exact matchRel_solution_iff (.varNonVar hnonvar hadmissible)
  next =>
      intro value varName hnonvar hadmissible
      exact matchRel_solution_iff (.nonVarVar hnonvar hadmissible)
  next =>
      intro left right out hitems hadmissible ih
      exact matchRel_solution_iff (.expression hitems hadmissible)
  next =>
      intro grounded right out hright hcustom hmatch hadmissible
      exact matchRel_solution_iff
        (.groundedLeftCustom hright hcustom hmatch hadmissible)
  next =>
      intro left grounded out hleft hleftNoCustom hcustom hmatch hadmissible
      exact matchRel_solution_iff
        (.groundedRightCustom hleft hleftNoCustom hcustom hmatch hadmissible)
  next =>
      intro left right hleft hright hadmissible
      exact matchRel_solution_iff
        (.groundedFallback hleft hright hadmissible)
  next =>
      intro seed valuation
      simp
  next =>
      intro left right lefts rights seed matched next out
        hmatch hmerge htail ihMatch ihMerge ihTail valuation
      rw [ihTail valuation, ihMerge valuation, ihMatch valuation]
      simp only [toLeaTTaAtoms_cons, List.map_cons, List.cons.injEq]
      tauto
  next =>
      intro bindings varName value hvalues valuation
      exact hesat_assign_of_not_isBound
        (isBound_eq_false_of_classValues_nil hvalues) valuation
  next =>
      intro bindings varName value first rest hvalues hagree hvalue
      subst value
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      constructor
      · intro hsat
        exact ⟨hsat,
          hsat.eq_applyClassSolution_of_mem_classValues hfirst⟩
      · exact fun hsat => hsat.1
  next =>
      intro bindings varName value first rest matched out hvalues hagree
        hne hmatch hmerge ihMatch ihMerge
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihMatch valuation]
      have hvalue : HEBindingSatisfied valuation bindings →
          valuation varName =
            applyClassSolution valuation (toLeaTTaAtom first) :=
        fun hsat => hsat.eq_applyClassSolution_of_mem_classValues hfirst
      constructor
      · rintro ⟨hsat, hmatched⟩
        exact ⟨hsat, (hvalue hsat).trans hmatched⟩
      · rintro ⟨hsat, hnew⟩
        exact ⟨hsat, (hvalue hsat).symm.trans hnew⟩
  next =>
      intro bindings varName value first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihList valuation]
      simp only [hesat_empty_iff, true_and,
        solutionTheory_toLeaTTaAtoms_eq_map, List.map_map,
        List.map_replicate]
      rw [show rest.length + 1 = (rest ++ [value]).length by simp]
      rw [replicate_eq_map_iff valuation first (rest ++ [value])]
      have hhead : HEBindingSatisfied valuation bindings →
          valuation varName =
            applyClassSolution valuation (toLeaTTaAtom first) :=
        fun hsat => hsat.eq_applyClassSolution_of_mem_classValues hfirst
      have hrest : HEBindingSatisfied valuation bindings →
          ∀ atom ∈ rest,
            applyClassSolution valuation (toLeaTTaAtom atom) =
              applyClassSolution valuation (toLeaTTaAtom first) := by
        intro hsat atom hatom
        have hclass : atom ∈ bindings.classValues varName :=
          (List.Perm.mem_iff hvalues).mp (by simp [hatom])
        exact
          (hsat.eq_applyClassSolution_of_mem_classValues hclass).symm.trans
            (hhead hsat)
      constructor
      · rintro ⟨hsat, hall⟩
        have hnew := hall value (List.mem_append_right rest (by simp))
        exact ⟨hsat, (hhead hsat).trans hnew.symm⟩
      · rintro ⟨hsat, hnew⟩
        refine ⟨hsat, fun atom hatom => ?_⟩
        rcases List.mem_append.mp hatom with hatom | hatom
        · exact hrest hsat atom hatom
        · simp only [List.mem_singleton] at hatom
          subst atom
          exact ((hhead hsat).symm.trans hnew).symm
  next =>
      intro bindings left right values hvalues hagree valuation
      exact hesat_addEquality valuation
  next =>
      intro bindings left right first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      have hfirst : first ∈
          (bindings.addEquality left right).classValues left :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihList valuation, hesat_addEquality]
      simp only [hesat_empty_iff, true_and,
        solutionTheory_toLeaTTaAtoms_eq_map, List.map_map,
        List.map_replicate]
      rw [replicate_eq_map_iff valuation first rest]
      have hall : HEBindingSatisfied valuation
            (bindings.addEquality left right) →
          ∀ atom ∈ rest,
            applyClassSolution valuation (toLeaTTaAtom atom) =
              applyClassSolution valuation (toLeaTTaAtom first) := by
        intro hsat atom hatom
        have hheadSat :=
          hsat.eq_applyClassSolution_of_mem_classValues hfirst
        have hclass : atom ∈
            (bindings.addEquality left right).classValues left :=
          (List.Perm.mem_iff hvalues).mp (by simp [hatom])
        exact
          (hsat.eq_applyClassSolution_of_mem_classValues hclass).symm.trans
            hheadSat
      constructor
      · rintro ⟨hsat, hallMatched⟩
        exact hsat
      · intro hsat
        have hcandidate := (hesat_addEquality valuation).mpr hsat
        exact ⟨hsat, hall hcandidate⟩
  next =>
      intro seed valuation
      simp [ConstraintsSatisfied]
  next =>
      intro seed next out varName value rest hadd htail ihAdd ihTail valuation
      rw [ihTail valuation, ihAdd valuation]
      simp [ConstraintsSatisfied, ConstraintSatisfied, and_assoc]
  next =>
      intro seed next out left right rest hadd htail ihAdd ihTail valuation
      rw [ihTail valuation, ihAdd valuation]
      simp [ConstraintsSatisfied, ConstraintSatisfied, and_assoc]
  next =>
      intro left right out order hperm hfold ihFold valuation
      rw [ihFold valuation,
        constraintsSatisfied_iff_of_perm hperm,
        constraintsSatisfied_constraints_iff]

/-- Pointwise spec list matching presents the live seed theory together with
the pointwise equations.  This projection is useful when a recursive class
reconciliation consumes its transient match record during merge-back. -/
theorem matchListAccRel_solution_iff
    {left right : List Atom} {seed out : Bindings}
    (derivation : Spec.Match.Merge.MatchListAccRel
      Spec.Match.Merge.equalityGroundedSemantic left right seed out)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation out ↔
      HEBindingSatisfied valuation seed ∧
        (toLeaTTaAtoms left).map (applyClassSolution valuation) =
          (toLeaTTaAtoms right).map (applyClassSolution valuation) := by
  apply Spec.Match.Merge.MatchListAccRel.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun left right seed out _ =>
      HEBindingSatisfied valuation out ↔
        HEBindingSatisfied valuation seed ∧
          (toLeaTTaAtoms left).map (applyClassSolution valuation) =
            (toLeaTTaAtoms right).map (applyClassSolution valuation))
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (t := derivation)
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => simp
  next =>
      intro headLeft headRight tailLeft tailRight live matched next out
        hhead hmerge htail ihHead ihMerge ihTail
      rw [ihTail, mergeRel_solution_iff hmerge valuation,
        matchRel_solution_iff hhead valuation]
      simp only [toLeaTTaAtoms, List.map_cons, List.cons.injEq]
      aesop
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial

/-- Any two specification derivations of the same match have the same complete
binding solution theory.  In particular, constraint order, equality-edge
orientation, representative chronology, and reconciliation path cannot be
observed through binding satisfaction. -/
theorem matchRel_solutionTheory_unique
    {left right : Atom} {first second : Bindings}
    (hfirst : Spec.Match.Merge.MatchRel
      Spec.Match.Merge.equalityGroundedSemantic left right first)
    (hsecond : Spec.Match.Merge.MatchRel
      Spec.Match.Merge.equalityGroundedSemantic left right second) :
    ∀ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation first ↔
        HEBindingSatisfied valuation second := by
  intro valuation
  exact (matchRel_solution_iff hfirst valuation).trans
    (matchRel_solution_iff hsecond valuation).symm

namespace Controls

/-- The independent source constructs an alias without choosing an evaluator. -/
theorem shared_alias_derivation :
    Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic
      (.var "left") (.var "right")
      (Bindings.empty.addEquality "left" "right") :=
  .varVar "left" "right"
    (Spec.Match.Merge.semanticLoopFree_of_assignments_nil rfl)

/-- One source alias constrains both observations to the same value. -/
theorem shared_alias_model_iff (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation (Bindings.empty.addEquality "left" "right") ↔
      valuation "left" = valuation "right" := by
  simpa using matchRel_solution_iff shared_alias_derivation valuation

/-- Assigning distinct values to the two ends violates that same source model. -/
theorem unequal_alias_images_rejected :
    ¬HEBindingSatisfied
      (fun name => if name = "left" then .sym "a" else .sym "b")
      (Bindings.empty.addEquality "left" "right") := by
  rw [shared_alias_model_iff]
  simp

/-- A repeated physical equality row keeps the same model constraint. -/
theorem duplicate_alias_same_models (bindings : Bindings)
    (left right : String) (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation
        ((bindings.addEquality left right).addEquality left right) ↔
      HEBindingSatisfied valuation (bindings.addEquality left right) := by
  simp only [hesat_addEquality]
  tauto

end Controls

end Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory


namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open LeaTTaBridge

/-- Total decoding of LeaTTa grounded payloads into the spec atom language.
Runtime-only constructors are retained as explicitly tagged custom
payloads; no conformance claim is made for their operational behavior. -/
def fromLeaTTaGround : Metta.Ground → GroundedValue
  | .int value => .int value
  | .float _ => .custom "%LeaFloat%" ""
  | .str value => .string value
  | .bool value => .bool value
  | .unit => .custom "%LeaUnit%" ""
  | .error message => .custom "%LeaError%" message
  | .external typeName payload => .custom typeName payload
  | .bindings relations => .custom "%LeaBindings%" (reprStr relations)

mutual

/-- Total structural decoding from LeaTTa atoms to native HE atoms. -/
def fromLeaTTaAtom : Metta.Atom → Atom
  | .sym name => .symbol name
  | .var name => .var name
  | .gnd value => .grounded (fromLeaTTaGround value)
  | .expr atoms => .expression (fromLeaTTaAtoms atoms)

/-- List companion of `fromLeaTTaAtom`. -/
def fromLeaTTaAtoms : List Metta.Atom → List Atom
  | [] => []
  | atom :: atoms => fromLeaTTaAtom atom :: fromLeaTTaAtoms atoms

end

@[simp] theorem fromLeaTTaGround_toLeaTTaGround (value : GroundedValue) :
    fromLeaTTaGround (toLeaTTaGround value) = value := by
  cases value <;> rfl

theorem toLeaTTaAtoms_eq_map (atoms : List Atom) :
    toLeaTTaAtoms atoms = atoms.map toLeaTTaAtom := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [toLeaTTaAtoms, ih]

@[simp] theorem fromLeaTTaAtoms_eq_map (atoms : List Metta.Atom) :
    fromLeaTTaAtoms atoms = atoms.map fromLeaTTaAtom := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [fromLeaTTaAtoms, ih]

mutual

@[simp] theorem fromLeaTTaAtom_toLeaTTaAtom (atom : Atom) :
    fromLeaTTaAtom (toLeaTTaAtom atom) = atom := by
  cases atom with
  | symbol | var | grounded =>
      simp [toLeaTTaAtom, fromLeaTTaAtom]
  | expression atoms =>
      exact congrArg Atom.expression
        (fromLeaTTaAtoms_toLeaTTaAtoms atoms)
termination_by 2 * sizeOf atom

@[simp] theorem fromLeaTTaAtoms_toLeaTTaAtoms (atoms : List Atom) :
    fromLeaTTaAtoms (toLeaTTaAtoms atoms) = atoms := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (fromLeaTTaAtom_toLeaTTaAtom atom)
        (fromLeaTTaAtoms_toLeaTTaAtoms atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end


end Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
