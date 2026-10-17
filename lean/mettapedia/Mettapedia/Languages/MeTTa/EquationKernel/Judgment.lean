import Mettapedia.Languages.MeTTa.SubstitutionAlgebra
import Mettapedia.Languages.MeTTa.OSLFCore.Atomspace
import Mathlib.Logic.Relation

/-!
# Equation application over atoms

A space is a multiset of atoms. A stored equation `(= l r)` licenses the
replacement of an instance `σ l` by `σ r` at any position of an atom. The
judgment `Reaches space a b` is the reflexive-transitive closure of that
step: the positive, existential claim that `b` is obtained from `a` by finitely
many equation applications. It fixes no evaluation order, and it allows a
step at any position, including positions that a dialect's evaluator never
rewrites. It does not say that `b` is irreducible, nor that `b` is a result
of a particular dialect's evaluation strategy; those are stronger judgments
with absence evidence.

The substitution of a step instantiates the equation only. Variables of the
subject are constants of the claim, so no instance captures or instantiates
them. The step relation is nevertheless stable under substituting the whole
claim (`Step.substitute`): a supplied unifier licenses rewriting the
instantiated subject (`narrowing_step` in `Hygiene`).

The four kernel rules `Derives` are reflexivity, one equation application
at a position of an already derived endpoint, congruence in one argument, and
transitivity. They generate exactly `Reaches` (`derives_iff_reaches`), and
reflexivity and the step rule alone already do (`Derives.of_reaches` uses only
those two): congruence and transitivity serve sharing and composition. Both
the certificate checker and the sealed-theorem kernel are built from these
rules.

Positions are lists of argument indices. `Context` is the one-hole context
view of the same positions; `subatom?_fill`, `replaceAt?_fill` and
`exists_context_of_subatom?` translate between them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EquationKernel

open Mettapedia.Languages.MeTTa.OSLFCore (Atom Atomspace)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Var Subst subst vars)

/-! ## Spaces and equations -/

/-- The space of a program: the program's atoms as a multiset. Order is
forgotten and multiplicity is kept. -/
def spaceOf (program : List Atom) : Atomspace := ⟨↑program⟩

theorem spaceOf_perm {program other : List Atom} (permuted : program.Perm other) :
    spaceOf program = spaceOf other := by
  unfold spaceOf
  rw [Multiset.coe_eq_coe.mpr permuted]

/-- The two lawful equality tests on atoms count alike. -/
theorem count_decidable_eq (program : List Atom) (atom : Atom) :
    @List.count Atom instBEqOfDecidableEq atom program = program.count atom :=
  congrArg (fun test : BEq Atom => @List.count Atom test atom program)
    (lawful_beq_subsingleton _ _)

theorem count_spaceOf (program : List Atom) (atom : Atom) :
    (spaceOf program).atoms.count atom = program.count atom := by
  unfold spaceOf
  rw [Multiset.coe_count, count_decidable_eq]

theorem mem_spaceOf {program : List Atom} {atom : Atom} :
    atom ∈ (spaceOf program).atoms ↔ atom ∈ program :=
  Multiset.mem_coe

/-- The two sides of an equation atom `(= l r)`. -/
def equationSides : Atom → Option (Atom × Atom)
  | .expression [head, left, right] =>
      if head = .symbol "=" then some (left, right) else none
  | _ => none

theorem equationSides_equality (left right : Atom) :
    equationSides (Atom.equality left right) = some (left, right) := by
  simp [equationSides, Atom.equality]

theorem equationSides_eq_some {equation left right : Atom} :
    equationSides equation = some (left, right) ↔ equation = Atom.equality left right := by
  constructor
  · intro sides
    unfold equationSides at sides
    split at sides
    · rename_i head l r
      split_ifs at sides with isEquals
      cases sides
      subst isEquals
      rfl
    · cases sides
  · rintro rfl
    exact equationSides_equality left right

/-! ## Substitution on expressions -/

theorem substList_eq_map (σ : Subst) :
    ∀ atoms : List Atom, subst.substList σ atoms = atoms.map (subst σ)
  | [] => rfl
  | atom :: atoms => by
      simp only [subst.substList, List.map_cons, substList_eq_map σ atoms]

theorem subst_expression (σ : Subst) (atoms : List Atom) :
    subst σ (.expression atoms) = .expression (atoms.map (subst σ)) := by
  simp only [subst, substList_eq_map]

/-! ## Positions -/

/-- The subatom at a path of argument indices. -/
def subatom? : Atom → List Nat → Option Atom
  | atom, [] => some atom
  | .expression atoms, index :: path =>
      match atoms[index]? with
      | some atom => subatom? atom path
      | none => none
  | _, _ :: _ => none

/-- Replace the subatom at a path. -/
def replaceAt? : Atom → List Nat → Atom → Option Atom
  | _, [], replacement => some replacement
  | .expression atoms, index :: path, replacement =>
      match atoms[index]? with
      | some atom => (replaceAt? atom path replacement).map
          (fun replaced => .expression (atoms.set index replaced))
      | none => none
  | _, _ :: _, _ => none

/-- A one-hole context: the hole sits in one argument of an expression, with
the other arguments kept literally. -/
inductive Context where
  | hole
  | arg (left : List Atom) (inner : Context) (right : List Atom)
  deriving DecidableEq, Repr

def Context.fill : Context → Atom → Atom
  | .hole, atom => atom
  | .arg left inner right, atom => .expression (left ++ inner.fill atom :: right)

/-- The path of argument indices leading to the hole. -/
def Context.path : Context → List Nat
  | .hole => []
  | .arg left inner _ => left.length :: inner.path

/-- Contexts compose: `(outer.comp inner).fill a = outer.fill (inner.fill a)`. -/
def Context.comp : Context → Context → Context
  | .hole, inner => inner
  | .arg left outer right, inner => .arg left (outer.comp inner) right

theorem Context.comp_fill (outer inner : Context) (atom : Atom) :
    (outer.comp inner).fill atom = outer.fill (inner.fill atom) := by
  induction outer with
  | hole => rfl
  | arg left outer right ih => simp only [Context.comp, Context.fill, ih]

theorem subatom?_fill (context : Context) (atom : Atom) :
    subatom? (context.fill atom) context.path = some atom := by
  induction context with
  | hole => rfl
  | arg left inner right ih =>
      simp only [Context.fill, Context.path, subatom?]
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      simpa using ih

theorem replaceAt?_fill (context : Context) (atom replacement : Atom) :
    replaceAt? (context.fill atom) context.path replacement = some (context.fill replacement) := by
  induction context with
  | hole => rfl
  | arg left inner right ih =>
      simp only [Context.fill, Context.path, replaceAt?]
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      simp only [List.getElem?_cons_zero, ih, Option.map_some]
      congr 2
      rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
      rfl

/-- Every successful path lookup is the path of a context, and replacement at
that path is filling the same context. -/
theorem exists_context_of_subatom? :
    ∀ {atom : Atom} {path : List Nat} {focus : Atom},
      subatom? atom path = some focus →
        ∃ context : Context, context.path = path ∧ context.fill focus = atom ∧
          ∀ replacement, replaceAt? atom path replacement = some (context.fill replacement)
  | atom, [], focus, found => by
      cases found
      exact ⟨.hole, rfl, rfl, fun _ => rfl⟩
  | .expression atoms, index :: path, focus, found => by
      simp only [subatom?] at found
      split at found
      · rename_i child lookup
        obtain ⟨inner, innerPath, innerFill, innerReplace⟩ :=
          exists_context_of_subatom? found
        have bound : index < atoms.length := (List.getElem?_eq_some_iff.mp lookup).1
        have atIndex : atoms[index] = child := (List.getElem?_eq_some_iff.mp lookup).2
        refine ⟨.arg (atoms.take index) inner (atoms.drop (index + 1)), ?_, ?_, ?_⟩
        · simp only [Context.path, List.length_take, innerPath]
          rw [Nat.min_eq_left (Nat.le_of_lt bound)]
        · simp only [Context.fill, innerFill]
          rw [← atIndex, ← List.drop_eq_getElem_cons bound, List.take_append_drop]
        · intro replacement
          simp only [replaceAt?, lookup, innerReplace, Option.map_some, Context.fill]
          rw [List.set_eq_take_append_cons_drop, if_pos bound]
      · cases found
  | .symbol _, _ :: _, _, found => by cases found
  | .var _, _ :: _, _, found => by cases found
  | .grounded _, _ :: _, _, found => by cases found

/-! ## Substitution through contexts -/

/-- Apply a substitution to the kept arguments of a context. -/
def Context.substitute (σ : Subst) : Context → Context
  | .hole => .hole
  | .arg left inner right =>
      .arg (left.map (subst σ)) (inner.substitute σ) (right.map (subst σ))

theorem Context.substitute_fill (σ : Subst) (context : Context) (atom : Atom) :
    subst σ (context.fill atom) = (context.substitute σ).fill (subst σ atom) := by
  induction context with
  | hole => rfl
  | arg left inner right ih =>
      simp only [Context.fill, Context.substitute, subst_expression, List.map_append,
        List.map_cons, ih]

/-! ## The step relation and its closure -/

/-- One equation application: an instance of a stored equation's left side,
in any context, is replaced by the same instance of its right side. -/
inductive Step (space : Atomspace) : Atom → Atom → Prop
  | rewrite {left right : Atom} (context : Context) (σ : Subst) :
      Atom.equality left right ∈ space.atoms →
      Step space (context.fill (subst σ left)) (context.fill (subst σ right))

/-- Finitely many equation applications. -/
abbrev Reaches (space : Atomspace) : Atom → Atom → Prop :=
  Relation.ReflTransGen (Step space)

theorem Step.of_path {space : Atomspace} {left right source target : Atom}
    {path : List Nat} {σ : Subst}
    (stored : Atom.equality left right ∈ space.atoms)
    (found : subatom? source path = some (subst σ left))
    (replaced : replaceAt? source path (subst σ right) = some target) :
    Step space source target := by
  obtain ⟨context, _, fill, replace⟩ := exists_context_of_subatom? found
  rw [replace] at replaced
  cases replaced
  rw [← fill]
  exact .rewrite context σ stored

/-- A step happens at the path of its context. -/
theorem Step.exists_path {space : Atomspace} {source target : Atom}
    (step : Step space source target) :
    ∃ left right path σ, Atom.equality left right ∈ space.atoms ∧
      subatom? source path = some (subst σ left) ∧
      replaceAt? source path (subst σ right) = some target := by
  cases step with
  | rewrite context σ stored =>
      exact ⟨_, _, context.path, σ, stored, subatom?_fill _ _, replaceAt?_fill _ _ _⟩

theorem Step.in_context {space : Atomspace} {source target : Atom}
    (outer : Context) (step : Step space source target) :
    Step space (outer.fill source) (outer.fill target) := by
  cases step with
  | rewrite context σ stored =>
      simpa only [Context.comp_fill] using Step.rewrite (outer.comp context) σ stored

theorem Reaches.in_context {space : Atomspace} {source target : Atom}
    (outer : Context) (reaches : Reaches space source target) :
    Reaches space (outer.fill source) (outer.fill target) := by
  induction reaches with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.in_context outer)

/-- Instances of steps are steps: substituting the whole claim keeps it
derivable, because the subject's variables were constants of the step. -/
theorem Step.substitute {space : Atomspace} {source target : Atom} (θ : Subst)
    (step : Step space source target) :
    Step space (subst θ source) (subst θ target) := by
  cases step with
  | rewrite context σ stored =>
      rw [Context.substitute_fill, Context.substitute_fill, SubstitutionAlgebra.subst_subst,
        SubstitutionAlgebra.subst_subst]
      exact .rewrite (context.substitute θ) (SubstitutionAlgebra.comp σ θ) stored

theorem Reaches.substitute {space : Atomspace} {source target : Atom} (θ : Subst)
    (reaches : Reaches space source target) :
    Reaches space (subst θ source) (subst θ target) := by
  induction reaches with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.substitute θ)

theorem Reaches.mono {space other : Atomspace} {source target : Atom}
    (included : ∀ atom, atom ∈ space.atoms → atom ∈ other.atoms)
    (reaches : Reaches space source target) : Reaches other source target := by
  induction reaches with
  | refl => exact .refl
  | tail _ step ih =>
      cases step with
      | rewrite context σ stored => exact ih.tail (.rewrite context σ (included _ stored))

/-! ## The kernel rules -/

/-- The four kernel rules. A sealed theorem is minted only by these rules, and
a certificate row names one of them. -/
inductive Derives (space : Atomspace) : Atom → Atom → Prop
  | refl (atom : Atom) : Derives space atom atom
  | step {source current next left right : Atom} (path : List Nat) (σ : Subst) :
      Derives space source current →
      Atom.equality left right ∈ space.atoms →
      subatom? current path = some (subst σ left) →
      replaceAt? current path (subst σ right) = some next →
      Derives space source next
  | congr {source target : Atom} (left right : List Atom) :
      Derives space source target →
      Derives space (.expression (left ++ source :: right))
        (.expression (left ++ target :: right))
  | trans {first middle last : Atom} :
      Derives space first middle → Derives space middle last → Derives space first last

theorem Derives.reaches {space : Atomspace} {source target : Atom}
    (derived : Derives space source target) : Reaches space source target := by
  induction derived with
  | refl => exact .refl
  | step _ _ _ stored found replaced ih => exact ih.tail (Step.of_path stored found replaced)
  | congr left right _ ih => exact ih.in_context (.arg left .hole right)
  | trans _ _ first second => exact first.trans second

theorem Derives.of_reaches {space : Atomspace} {source target : Atom}
    (reaches : Reaches space source target) : Derives space source target := by
  induction reaches with
  | refl => exact .refl _
  | tail _ step ih =>
      obtain ⟨_, _, path, σ, stored, found, replaced⟩ := step.exists_path
      exact .step path σ ih stored found replaced

/-- The kernel rules generate exactly the reachability judgment. -/
theorem derives_iff_reaches {space : Atomspace} {source target : Atom} :
    Derives space source target ↔ Reaches space source target :=
  ⟨Derives.reaches, Derives.of_reaches⟩

/-- The judgment depends on the space only as a multiset. -/
theorem reaches_perm {program other : List Atom} (permuted : program.Perm other)
    {source target : Atom} :
    Reaches (spaceOf program) source target ↔ Reaches (spaceOf other) source target := by
  rw [spaceOf_perm permuted]

/-! ## Finite bindings and stored copies -/

/-- A finite substitution, as certificate data. Unlisted variables are left
unchanged. -/
abbrev Bindings := List (Var × Atom)

def Bindings.toSubst (bindings : Bindings) : Subst := fun name => bindings.lookup name

/-- One stored copy of an equation: its content and an index among its equal
copies. Content citation needs no order of the space. -/
structure Citation where
  equation : Atom
  copy : Nat
  deriving DecidableEq, Repr

/-- The cited copy exists in the space. -/
def Citation.Valid (space : Atomspace) (citation : Citation) : Prop :=
  citation.copy < space.atoms.count citation.equation

theorem Citation.valid_spaceOf {program : List Atom} {citation : Citation} :
    citation.Valid (spaceOf program) ↔ citation.copy < program.count citation.equation := by
  rw [Citation.Valid, count_spaceOf]

theorem Citation.Valid.mem {space : Atomspace} {citation : Citation}
    (valid : citation.Valid space) : citation.equation ∈ space.atoms :=
  Multiset.count_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) valid)

theorem Citation.exists_valid {space : Atomspace} {equation : Atom}
    (stored : equation ∈ space.atoms) : (Citation.mk equation 0).Valid space :=
  Multiset.count_pos.mpr stored

/-- Every stored copy, each exactly once. A copy's index counts the equal
atoms before it; the set of citations does not depend on that order
(`occurrences_perm`). -/
def occurrencesFrom (seen : List Atom) : List Atom → List Citation
  | [] => []
  | equation :: rest => ⟨equation, seen.count equation⟩ :: occurrencesFrom (equation :: seen) rest

def occurrences (program : List Atom) : List Citation := occurrencesFrom [] program

theorem mem_occurrencesFrom (seen rest : List Atom) (citation : Citation) :
    citation ∈ occurrencesFrom seen rest ↔
      seen.count citation.equation ≤ citation.copy ∧
        citation.copy < seen.count citation.equation + rest.count citation.equation := by
  induction rest generalizing seen with
  | nil =>
      simp only [occurrencesFrom, List.not_mem_nil, List.count_nil, Nat.add_zero, false_iff]
      omega
  | cons equation rest ih =>
      rcases citation with ⟨cited, copy⟩
      simp only [occurrencesFrom, List.mem_cons, Citation.mk.injEq, ih]
      by_cases same : cited = equation
      · subst same
        simp only [List.count_cons_self, true_and]
        omega
      · have skip : (equation == cited) = false := by
          simpa [beq_iff_eq] using Ne.symm same
        simp only [List.count_cons, skip, same, false_and, false_or]
        simp

theorem mem_occurrences {program : List Atom} {citation : Citation} :
    citation ∈ occurrences program ↔ citation.copy < program.count citation.equation := by
  simp [occurrences, mem_occurrencesFrom]

theorem occurrencesFrom_nodup (seen rest : List Atom) : (occurrencesFrom seen rest).Nodup := by
  induction rest generalizing seen with
  | nil => exact List.nodup_nil
  | cons equation rest ih =>
      refine List.nodup_cons.mpr ⟨?_, ih _⟩
      intro member
      have := ((mem_occurrencesFrom _ _ _).mp member).1
      simp only [List.count_cons_self] at this
      omega

theorem occurrences_nodup (program : List Atom) : (occurrences program).Nodup :=
  occurrencesFrom_nodup [] program

theorem occurrencesFrom_equations (seen rest : List Atom) :
    (occurrencesFrom seen rest).map Citation.equation = rest := by
  induction rest generalizing seen with
  | nil => rfl
  | cons equation rest ih => simp only [occurrencesFrom, List.map_cons, ih]

/-- Counting stored copies: the occurrences whose equation has a property
are exactly as many as the program's atoms with that property. -/
theorem occurrences_filter_length (program : List Atom) (property : Atom → Bool) :
    ((occurrences program).filter (fun citation => property citation.equation)).length =
      (program.filter property).length := by
  have mapped := congrArg (List.filter property) (occurrencesFrom_equations [] program)
  rw [List.filter_map] at mapped
  have lengths := congrArg List.length mapped
  rw [List.length_map] at lengths
  exact lengths

/-- Reordering the program permutes its stored copies. -/
theorem occurrences_perm {program other : List Atom} (permuted : program.Perm other) :
    (occurrences program).Perm (occurrences other) := by
  refine (List.perm_ext_iff_of_nodup (occurrences_nodup _) (occurrences_nodup _)).mpr ?_
  intro citation
  rw [mem_occurrences, mem_occurrences, permuted.count_eq]

end Mettapedia.Languages.MeTTa.EquationKernel
