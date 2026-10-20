import Mettapedia.Logic.Relation.CommutativeTerms

/-!
# Which conversions rewrite rules can present with normal forms

The meet-closed fiber has a definability theorem: a family of bubbles is the
family of models of a Horn theory exactly when it is closed under
intersections (`SufficientBubbles.leastAbove_iff_hornDefinable`).  This module
proves the counterpart for the normal-form fiber: which equivalences are the
conversion of rule schemas whose normal forms decide them.

A **term structure** (`TermStructure`) has one-hole contexts that compose and
substitutions that act on terms, a substitution entering a context uniformly.
Rules given by schemas are a root relation closed under every substitution
(`Schematic`); their steps are root steps under contexts (`Step`).

**Theorem** (`exists_presentation_iff`).  An equivalence `E` is the conversion
of a schematic root relation whose conversion is decided by normal forms on
every term exactly when

* `E` is closed under contexts and substitutions (`FullyInvariant`), and
* `E` has a transversal, one representative in each class (`Transversal`),
  that is closed under taking subterms (`SubtermClosed`) and reflects
  substitution instances: if an instance is a representative, so is the term
  (`InstanceReflecting`).

The representatives are then the normal forms (`normalForms_of_presentation`).
Conversely, from such a transversal the rules `σ(s) ↦ σ(rep s)`, for `s` not a
representative, present `E` (`presentation_of_transversal`).

Symmetric classes have no such transversal when a substitution exchanges two
variables: an instance-reflecting transversal is closed under the exchange, so
its member in a class preserved by the exchange is fixed by it.  On binary
terms, commutativity has no subterm-closed, instance-reflecting transversal
(`commEq_no_transversal`), so no rule schemas present it with normal forms;
associativity has one, the right-nested terms
(`assoc_presentation`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Relation.SchematicPresentation

open _root_.Relation
open Mettapedia.Logic.Relation (IsNormal IsNormalFormOf DecidedOn decidedOn_iff_uniqueNormalForms)

universe u

/-- Terms with one-hole contexts that compose and substitutions that act,
a substitution entering a context uniformly. -/
structure TermStructure (α : Type u) where
  Ctx : Type u
  plug : Ctx → α → α
  hole : Ctx
  plug_hole : ∀ t, plug hole t = t
  comp : Ctx → Ctx → Ctx
  plug_comp : ∀ C D t, plug (comp C D) t = plug C (plug D t)
  Sub : Type u
  act : Sub → α → α
  idSub : Sub
  act_id : ∀ t, act idSub t = t
  mul : Sub → Sub → Sub
  act_mul : ∀ σ τ t, act (mul σ τ) t = act σ (act τ t)
  act_plug : ∀ σ C, ∃ C' σ', ∀ t, act σ (plug C t) = plug C' (act σ' t)

variable {α : Type u} (T : TermStructure α)

/-- A root relation closed under every substitution: the instances of rule
schemas. -/
def Schematic (ρ : α → α → Prop) : Prop :=
  ∀ σ l r, ρ l r → ρ (T.act σ l) (T.act σ r)

/-- A root step under a context. -/
def Step (ρ : α → α → Prop) (source target : α) : Prop :=
  ∃ C l r, ρ l r ∧ source = T.plug C l ∧ target = T.plug C r

/-- An equivalence closed under contexts and substitutions. -/
def FullyInvariant (E : α → α → Prop) : Prop :=
  Equivalence E ∧ (∀ C a b, E a b → E (T.plug C a) (T.plug C b)) ∧
    ∀ σ a b, E a b → E (T.act σ a) (T.act σ b)

/-- One representative in each class. -/
def Transversal (E : α → α → Prop) (N : Set α) : Prop :=
  (∀ t, ∃ n ∈ N, E t n) ∧ ∀ n ∈ N, ∀ m ∈ N, E n m → n = m

/-- Closed under taking subterms. -/
def SubtermClosed (N : Set α) : Prop :=
  ∀ C t, T.plug C t ∈ N → t ∈ N

/-- If an instance is in the set, so is the term. -/
def InstanceReflecting (N : Set α) : Prop :=
  ∀ σ t, T.act σ t ∈ N → t ∈ N

/-- A schematic root relation whose conversion is `E` and is decided by
normal forms on every term. -/
def NormalFormPresentation (E : α → α → Prop) (ρ : α → α → Prop) : Prop :=
  Schematic T ρ ∧ (∀ a b, EqvGen (Step T ρ) a b ↔ E a b) ∧ DecidedOn (Step T ρ) Set.univ

variable {T}

theorem step_plug {ρ : α → α → Prop} {source target : α} (C : T.Ctx)
    (step : Step T ρ source target) : Step T ρ (T.plug C source) (T.plug C target) := by
  obtain ⟨D, l, r, rule, rfl, rfl⟩ := step
  exact ⟨T.comp C D, l, r, rule, (T.plug_comp C D l).symm, (T.plug_comp C D r).symm⟩

theorem step_act {ρ : α → α → Prop} (schematic : Schematic T ρ) {source target : α} (σ : T.Sub)
    (step : Step T ρ source target) : Step T ρ (T.act σ source) (T.act σ target) := by
  obtain ⟨C, l, r, rule, rfl, rfl⟩ := step
  obtain ⟨C', σ', distributes⟩ := T.act_plug σ C
  exact ⟨C', T.act σ' l, T.act σ' r, schematic σ' l r rule, distributes l, distributes r⟩

theorem eqvGen_plug {ρ : α → α → Prop} (C : T.Ctx) {a b : α} (converted : EqvGen (Step T ρ) a b) :
    EqvGen (Step T ρ) (T.plug C a) (T.plug C b) :=
  Mettapedia.Logic.Relation.EqvGen.map_of_steps (fun _ _ step => step_plug C step) converted

theorem eqvGen_act {ρ : α → α → Prop} (schematic : Schematic T ρ) (σ : T.Sub) {a b : α}
    (converted : EqvGen (Step T ρ) a b) : EqvGen (Step T ρ) (T.act σ a) (T.act σ b) :=
  Mettapedia.Logic.Relation.EqvGen.map_of_steps (fun _ _ step => step_act schematic σ step) converted

/-! ## From a presentation to a transversal -/

/-- **The normal forms of a presentation are a subterm-closed, instance-reflecting
transversal of its conversion**, and the conversion is fully invariant. -/
theorem normalForms_of_presentation {E ρ : α → α → Prop}
    (presentation : NormalFormPresentation T E ρ) :
    FullyInvariant T E ∧ Transversal E {t | IsNormal (Step T ρ) t} ∧
      SubtermClosed T {t | IsNormal (Step T ρ) t} ∧
      InstanceReflecting T {t | IsNormal (Step T ρ) t} := by
  obtain ⟨schematic, same, decided⟩ := presentation
  refine ⟨⟨?_, fun C a b related => ?_, fun σ a b related => ?_⟩, ⟨fun t => ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨fun a => (same a a).mp (EqvGen.refl a), fun related => ?_, fun first second => ?_⟩
    · exact (same _ _).mp (EqvGen.symm _ _ ((same _ _).mpr related))
    · exact (same _ _).mp (EqvGen.trans _ _ _ ((same _ _).mpr first) ((same _ _).mpr second))
  · exact (same _ _).mp (eqvGen_plug C ((same a b).mpr related))
  · exact (same _ _).mp (eqvGen_act schematic σ ((same a b).mpr related))
  · obtain ⟨n, normalForm⟩ := decided.1 t (Set.mem_univ t)
    exact ⟨n, normalForm.2, (same t n).mp normalForm.eqvGen⟩
  · intro n normalN m normalM related
    exact (decided.2 n (Set.mem_univ n) m (Set.mem_univ m) n m ⟨.refl, normalN⟩ ⟨.refl, normalM⟩).mp
      ((same n m).mpr related)
  · intro C t normal t' step
    exact normal _ (step_plug C step)
  · intro σ t normal t' step
    exact normal _ (step_act schematic σ step)

/-! ## From a transversal to a presentation -/

section FromTransversal

variable {E : α → α → Prop} {N : Set α}

/-- The representative of a term. -/
noncomputable def rep (transversal : Transversal E N) (t : α) : α :=
  Classical.choose (transversal.1 t)

theorem rep_mem (transversal : Transversal E N) (t : α) : rep transversal t ∈ N :=
  (Classical.choose_spec (transversal.1 t)).1

theorem rep_related (transversal : Transversal E N) (t : α) : E t (rep transversal t) :=
  (Classical.choose_spec (transversal.1 t)).2

theorem rep_eq_self (transversal : Transversal E N) {t : α}
    (member : t ∈ N) : rep transversal t = t :=
  (transversal.2 t member _ (rep_mem transversal t) (rep_related transversal t)).symm

variable (T)

/-- The rules `σ(s) ↦ σ(rep s)`, for every term `s` that is not a
representative and every substitution `σ`. -/
def transversalRules (transversal : Transversal E N) (l r : α) : Prop :=
  ∃ σ s, s ∉ N ∧ l = T.act σ s ∧ r = T.act σ (rep transversal s)

variable {T}

theorem transversalRules_schematic (transversal : Transversal E N) :
    Schematic T (transversalRules T transversal) := by
  rintro τ _ _ ⟨σ, s, notRep, rfl, rfl⟩
  exact ⟨T.mul τ σ, s, notRep, (T.act_mul τ σ s).symm, (T.act_mul τ σ _).symm⟩

theorem step_related (invariant : FullyInvariant T E) (transversal : Transversal E N) {a b : α}
    (step : Step T (transversalRules T transversal) a b) : E a b := by
  obtain ⟨C, l, r, ⟨σ, s, _, rfl, rfl⟩, rfl, rfl⟩ := step
  exact invariant.2.1 C _ _ (invariant.2.2 σ _ _ (rep_related transversal s))

theorem step_to_rep (transversal : Transversal E N) {t : α} (notRep : t ∉ N) :
    Step T (transversalRules T transversal) t (rep transversal t) :=
  ⟨T.hole, t, rep transversal t, ⟨T.idSub, t, notRep, (T.act_id t).symm, (T.act_id _).symm⟩,
    (T.plug_hole t).symm, (T.plug_hole _).symm⟩

theorem normal_of_mem (transversal : Transversal E N) (subterm : SubtermClosed T N)
    (reflecting : InstanceReflecting T N) {t : α} (member : t ∈ N) :
    IsNormal (Step T (transversalRules T transversal)) t := by
  rintro _ ⟨C, l, r, ⟨σ, s, notRep, rfl, rfl⟩, rfl, _⟩
  exact notRep (reflecting σ s (subterm C _ member))

/-- **A subterm-closed, instance-reflecting transversal of a fully invariant
equivalence gives a schematic presentation of it decided by normal forms.** -/
theorem presentation_of_transversal (invariant : FullyInvariant T E)
    (transversal : Transversal E N) (subterm : SubtermClosed T N)
    (reflecting : InstanceReflecting T N) :
    NormalFormPresentation T E (transversalRules T transversal) := by
  have toRep : ∀ t, ReflTransGen (Step T (transversalRules T transversal)) t (rep transversal t) := by
    intro t
    by_cases member : t ∈ N
    · rw [rep_eq_self transversal member]
    · exact .single (step_to_rep transversal member)
  have conversion : ∀ a b, EqvGen (Step T (transversalRules T transversal)) a b ↔ E a b := by
    intro a b
    constructor
    · intro converted
      induction converted with
      | rel _ _ step => exact step_related invariant transversal step
      | refl => exact invariant.1.refl _
      | symm _ _ _ ih => exact invariant.1.symm ih
      | trans _ _ _ _ _ first second => exact invariant.1.trans first second
    · intro related
      have same : rep transversal a = rep transversal b :=
        transversal.2 _ (rep_mem transversal a) _ (rep_mem transversal b)
          (invariant.1.trans (invariant.1.symm (rep_related transversal a))
            (invariant.1.trans related (rep_related transversal b)))
      exact EqvGen.trans _ _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (toRep a))
        (same ▸ EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (toRep b)))
  refine ⟨transversalRules_schematic transversal, conversion, ?_⟩
  refine decidedOn_iff_uniqueNormalForms.mpr ⟨fun t _ => ⟨rep transversal t, toRep t,
    normal_of_mem transversal subterm reflecting (rep_mem transversal t)⟩, ?_⟩
  intro _ _ _ _ n m normalN normalM converted
  have memberN : n ∈ N := by
    by_contra notRep
    exact normalN.2 _ (step_to_rep transversal notRep)
  have memberM : m ∈ N := by
    by_contra notRep
    exact normalM.2 _ (step_to_rep transversal notRep)
  exact transversal.2 n memberN m memberM ((conversion n m).mp converted)

end FromTransversal

/-- **An equivalence is presented by rule schemas with a decision by normal
forms exactly when it is fully invariant and has a subterm-closed,
instance-reflecting transversal.** -/
theorem exists_presentation_iff (E : α → α → Prop) :
    (∃ ρ, NormalFormPresentation T E ρ) ↔
      FullyInvariant T E ∧ ∃ N, Transversal E N ∧ SubtermClosed T N ∧ InstanceReflecting T N := by
  constructor
  · rintro ⟨ρ, presentation⟩
    obtain ⟨invariant, transversal, subterm, reflecting⟩ := normalForms_of_presentation presentation
    exact ⟨invariant, _, transversal, subterm, reflecting⟩
  · rintro ⟨invariant, N, transversal, subterm, reflecting⟩
    exact ⟨_, presentation_of_transversal invariant transversal subterm reflecting⟩

/-! ## Binary terms -/

namespace Binary

open Mettapedia.Logic.Relation.CommutativeTerms
open Bin

/-- One-hole contexts of binary terms. -/
inductive BinCtx where
  | hole : BinCtx
  | left : BinCtx → Bin → BinCtx
  | right : Bin → BinCtx → BinCtx

def plug : BinCtx → Bin → Bin
  | .hole, t => t
  | .left C b, t => op (plug C t) b
  | .right a C, t => op a (plug C t)

def comp : BinCtx → BinCtx → BinCtx
  | .hole, D => D
  | .left C b, D => .left (comp C D) b
  | .right a C, D => .right a (comp C D)

theorem plug_comp (C D : BinCtx) (t : Bin) : plug (comp C D) t = plug C (plug D t) := by
  induction C with
  | hole => rfl
  | left C b ih => simp [comp, plug, ih]
  | right a C ih => simp [comp, plug, ih]

/-- Substitution of terms for variables. -/
def subst (σ : Nat → Bin) : Bin → Bin
  | var n => σ n
  | op a b => op (subst σ a) (subst σ b)

theorem subst_var (t : Bin) : subst var t = t := by
  induction t with
  | var n => rfl
  | op a b iha ihb => simp [subst, iha, ihb]

theorem subst_subst (σ τ : Nat → Bin) (t : Bin) :
    subst (fun n => subst σ (τ n)) t = subst σ (subst τ t) := by
  induction t with
  | var n => rfl
  | op a b iha ihb => simp [subst, iha, ihb]

def substCtx (σ : Nat → Bin) : BinCtx → BinCtx
  | .hole => .hole
  | .left C b => .left (substCtx σ C) (subst σ b)
  | .right a C => .right (subst σ a) (substCtx σ C)

theorem subst_plug (σ : Nat → Bin) (C : BinCtx) (t : Bin) :
    subst σ (plug C t) = plug (substCtx σ C) (subst σ t) := by
  induction C with
  | hole => rfl
  | left C b ih => simp [plug, substCtx, subst, ih]
  | right a C ih => simp [plug, substCtx, subst, ih]

/-- Binary terms as a term structure. -/
def binTerms : TermStructure Bin where
  Ctx := BinCtx
  plug := plug
  hole := .hole
  plug_hole _ := rfl
  comp := comp
  plug_comp := plug_comp
  Sub := Nat → Bin
  act := subst
  idSub := var
  act_id := subst_var
  mul σ τ := fun n => subst σ (τ n)
  act_mul σ τ t := subst_subst σ τ t
  act_plug σ C := ⟨substCtx σ C, σ, fun t => subst_plug σ C t⟩

/-! ### Commutativity has no such transversal -/

/-- The substitution exchanging the variables `0` and `1`. -/
def swapSub : Nat → Bin := fun n => if n = 0 then var 1 else if n = 1 then var 0 else var n

theorem subst_swapSub (t : Bin) : subst swapSub t = swap01 t := by
  induction t with
  | var n => simp only [subst, swapSub, swap01, rename]; split_ifs <;> rfl
  | op a b iha ihb =>
      simp only [subst, swap01, rename] at iha ihb ⊢
      rw [iha, ihb]

theorem commStep_subst (σ : Nat → Bin) {a b : Bin} (step : CommStep a b) :
    CommStep (subst σ a) (subst σ b) := by
  induction step with
  | root a b => exact .root _ _
  | left b _ ih => exact .left _ ih
  | right a _ ih => exact .right _ ih

theorem commEq_subst (σ : Nat → Bin) {a b : Bin} (related : CommEq a b) :
    CommEq (subst σ a) (subst σ b) :=
  Mettapedia.Logic.Relation.EqvGen.map_of_steps (fun _ _ step => commStep_subst σ step) related

/-- **Commutativity has no instance-reflecting transversal**: the
representative of `x₀ ∘ x₁` would be fixed by the exchange of the two
variables. -/
theorem commEq_no_transversal :
    ¬ ∃ N : Set Bin, Transversal CommEq N ∧ InstanceReflecting binTerms N := by
  rintro ⟨N, transversal, reflecting⟩
  obtain ⟨n, member, related⟩ := transversal.1 (op (var 0) (var 1))
  have swappedMember : swap01 n ∈ N := by
    apply reflecting swapSub
    show subst swapSub (swap01 n) ∈ N
    rw [subst_swapSub, swap01_swap01]
    exact member
  have swappedRelated : CommEq (op (var 0) (var 1)) (swap01 n) := by
    have := commEq_subst swapSub related
    rw [subst_swapSub, subst_swapSub] at this
    exact EqvGen.trans _ _ _ (commEq_op _ _) (by simpa [swap01, rename] using this)
  have fixed : swap01 n = n :=
    transversal.2 _ swappedMember _ member
      (EqvGen.trans _ _ _ (EqvGen.symm _ _ swappedRelated) related)
  rcases commEq_op_vars related with rfl | rfl <;> simp [swap01, rename] at fixed

/-- **No rule schemas present commutativity with a decision by normal
forms.** -/
theorem commEq_no_presentation : ¬ ∃ ρ, NormalFormPresentation binTerms CommEq ρ := by
  rintro ⟨ρ, presentation⟩
  obtain ⟨_, transversal, _, reflecting⟩ := normalForms_of_presentation presentation
  exact commEq_no_transversal ⟨_, transversal, reflecting⟩

/-! ### Associativity has one -/

/-- Reassociation `(a ∘ b) ∘ c ↦ a ∘ (b ∘ c)`, at any position. -/
inductive AssocStep : Bin → Bin → Prop where
  | root (a b c : Bin) : AssocStep (op (op a b) c) (op a (op b c))
  | left {a a' : Bin} (b : Bin) : AssocStep a a' → AssocStep (op a b) (op a' b)
  | right (a : Bin) {b b' : Bin} : AssocStep b b' → AssocStep (op a b) (op a b')

/-- Associativity: the equivalence generated by reassociation. -/
abbrev AssocEq : Bin → Bin → Prop := EqvGen AssocStep

/-- The variables of a term, from left to right. -/
def leaves : Bin → List Nat
  | var n => [n]
  | op a b => leaves a ++ leaves b

theorem assocStep_leaves {a b : Bin} (step : AssocStep a b) : leaves a = leaves b := by
  induction step with
  | root a b c => simp [leaves, List.append_assoc]
  | left b _ ih => simp [leaves, ih]
  | right a _ ih => simp [leaves, ih]

theorem assocEq_leaves {a b : Bin} (related : AssocEq a b) : leaves a = leaves b := by
  induction related with
  | rel _ _ step => exact assocStep_leaves step
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- Right-nested terms: no operator has an operator as its left argument. -/
def RightNested : Bin → Prop
  | var _ => True
  | op (var _) b => RightNested b
  | op (op _ _) _ => False

/-- The right-nested term with the given nonempty list of leaves. -/
def nest : Nat → List Nat → Bin
  | n, [] => var n
  | n, m :: rest => op (var n) (nest m rest)

theorem nest_rightNested (n : Nat) (rest : List Nat) : RightNested (nest n rest) := by
  induction rest generalizing n with
  | nil => trivial
  | cons m rest ih => exact ih m

theorem leaves_nest (n : Nat) (rest : List Nat) : leaves (nest n rest) = n :: rest := by
  induction rest generalizing n with
  | nil => rfl
  | cons m rest ih => simp [nest, leaves, ih]

theorem leaves_length_pos (t : Bin) : 0 < (leaves t).length := by
  induction t with
  | var n => simp [leaves]
  | op a b iha _ => simp only [leaves, List.length_append]; omega

/-- A right-nested term is determined by its leaves. -/
theorem eq_of_rightNested {a b : Bin} (nestedA : RightNested a) (nestedB : RightNested b)
    (same : leaves a = leaves b) : a = b := by
  induction a generalizing b with
  | var n =>
      cases b with
      | var m => simpa [leaves] using same
      | op c d =>
          have length := congrArg List.length same
          have positive := leaves_length_pos c
          have positive' := leaves_length_pos d
          simp only [leaves, List.length_append, List.length_singleton] at length
          omega
  | op c d ihc ihd =>
      cases c with
      | op _ _ => exact nestedA.elim
      | var n =>
          cases b with
          | var m =>
              have length := congrArg List.length same
              have positive := leaves_length_pos d
              simp only [leaves, List.length_append, List.length_singleton] at length
              omega
          | op e f =>
              cases e with
              | op _ _ => exact nestedB.elim
              | var m =>
                  simp only [leaves, List.singleton_append, List.cons.injEq] at same
                  have nestedF : RightNested f := nestedB
                  rw [same.1, ihd nestedA nestedF same.2]

theorem assocEq_congr {a a' b b' : Bin} (left : AssocEq a a') (right : AssocEq b b') :
    AssocEq (op a b) (op a' b') := by
  have inLeft : ∀ {x x' : Bin} (y : Bin), AssocEq x x' → AssocEq (op x y) (op x' y) := by
    intro x x' y converted
    induction converted with
    | rel _ _ step => exact EqvGen.rel _ _ (.left y step)
    | refl => exact EqvGen.refl _
    | symm _ _ _ ih => exact EqvGen.symm _ _ ih
    | trans _ _ _ _ _ first second => exact EqvGen.trans _ _ _ first second
  have inRight : ∀ (x : Bin) {y y' : Bin}, AssocEq y y' → AssocEq (op x y) (op x y') := by
    intro x y y' converted
    induction converted with
    | rel _ _ step => exact EqvGen.rel _ _ (.right x step)
    | refl => exact EqvGen.refl _
    | symm _ _ _ ih => exact EqvGen.symm _ _ ih
    | trans _ _ _ _ _ first second => exact EqvGen.trans _ _ _ first second
  exact EqvGen.trans _ _ _ (inLeft b left) (inRight a' right)

/-- Append a term to the end of the right spine of a right-nested term. -/
def nappend : Bin → Bin → Bin
  | var n, y => op (var n) y
  | op (var n) x, y => op (var n) (nappend x y)
  | op (op a b) c, y => op (op (op a b) c) y

theorem nappend_rightNested {x y : Bin} (nestedX : RightNested x) (nestedY : RightNested y) :
    RightNested (nappend x y) := by
  induction x with
  | var n => exact nestedY
  | op a b _ ihb =>
      cases a with
      | var n => exact ihb nestedX
      | op _ _ => exact nestedX.elim

theorem assoc_nappend {x : Bin} (nestedX : RightNested x) (y : Bin) :
    AssocEq (op x y) (nappend x y) := by
  induction x with
  | var n => exact EqvGen.refl _
  | op a b _ ihb =>
      cases a with
      | var n =>
          exact EqvGen.trans _ _ _ (EqvGen.rel _ _ (.root _ _ _))
            (assocEq_congr (EqvGen.refl _) (ihb nestedX))
      | op _ _ => exact nestedX.elim

/-- The right-nested form, built bottom up. -/
def nestForm : Bin → Bin
  | var n => var n
  | op a b => nappend (nestForm a) (nestForm b)

theorem nestForm_rightNested (t : Bin) : RightNested (nestForm t) := by
  induction t with
  | var n => trivial
  | op a b iha ihb => exact nappend_rightNested iha ihb

theorem assocEq_nestForm (t : Bin) : AssocEq t (nestForm t) := by
  induction t with
  | var n => exact EqvGen.refl _
  | op a b iha ihb =>
      exact EqvGen.trans _ _ _ (assocEq_congr iha ihb)
        (assoc_nappend (nestForm_rightNested a) (nestForm b))

/-- **Associativity on binary terms is fully invariant.** -/
theorem assocEq_fullyInvariant : FullyInvariant binTerms AssocEq := by
  have stepPlug : ∀ (C : BinCtx) {a b : Bin}, AssocStep a b → AssocStep (plug C a) (plug C b) := by
    intro C a b step
    induction C with
    | hole => exact step
    | left C b' ih => exact .left b' ih
    | right a' C ih => exact .right a' ih
  have stepSubst : ∀ (σ : Nat → Bin) {a b : Bin}, AssocStep a b →
      AssocStep (subst σ a) (subst σ b) := by
    intro σ a b step
    induction step with
    | root a b c => exact .root _ _ _
    | left b _ ih => exact .left _ ih
    | right a _ ih => exact .right _ ih
  refine ⟨EqvGen.is_equivalence _, fun C a b related => ?_, fun σ a b related => ?_⟩
  · exact Mettapedia.Logic.Relation.EqvGen.map_of_steps (π := plug C)
      (fun _ _ step => stepPlug C step) related
  · exact Mettapedia.Logic.Relation.EqvGen.map_of_steps (π := subst σ)
      (fun _ _ step => stepSubst σ step) related

/-- **The right-nested terms are a transversal of associativity.** -/
theorem rightNested_transversal : Transversal AssocEq {t | RightNested t} :=
  ⟨fun t => ⟨nestForm t, nestForm_rightNested t, assocEq_nestForm t⟩,
    fun _ nestedN _ nestedM related =>
      eq_of_rightNested nestedN nestedM (assocEq_leaves related)⟩

theorem rightNested_subtermClosed : SubtermClosed binTerms {t | RightNested t} := by
  intro C t nested
  induction C with
  | hole => exact nested
  | left C b ih =>
      show RightNested t
      change RightNested (op (plug C t) b) at nested
      cases hplug : plug C t with
      | op _ _ => rw [hplug] at nested; exact nested.elim
      | var n =>
          cases C with
          | hole => simp only [plug] at hplug; rw [hplug]; trivial
          | left _ _ => simp [plug] at hplug
          | right _ _ => simp [plug] at hplug
  | right a C ih =>
      change RightNested (op a (plug C t)) at nested
      cases a with
      | var n => exact ih nested
      | op _ _ => exact nested.elim

theorem rightNested_instanceReflecting : InstanceReflecting binTerms {t | RightNested t} := by
  intro σ t nested
  change RightNested (subst σ t) at nested
  induction t with
  | var n => trivial
  | op a b _ ihb =>
      cases a with
      | var n =>
          simp only [subst] at nested
          cases hσ : σ n with
          | var m => rw [hσ] at nested; exact ihb nested
          | op _ _ => rw [hσ] at nested; exact nested.elim
      | op _ _ => simp [subst, RightNested] at nested

/-- The rules built from the right-nested transversal present associativity
with a decision by normal forms. -/
theorem assoc_transversalRules_presentation :
    NormalFormPresentation binTerms AssocEq (transversalRules binTerms rightNested_transversal) :=
  presentation_of_transversal assocEq_fullyInvariant rightNested_transversal
    rightNested_subtermClosed rightNested_instanceReflecting

/-- **Rule schemas present associativity with a decision by normal forms**,
the right-nested terms being the normal forms. -/
theorem assoc_presentation : ∃ ρ, NormalFormPresentation binTerms AssocEq ρ :=
  (exists_presentation_iff AssocEq).mpr ⟨assocEq_fullyInvariant, _, rightNested_transversal,
    rightNested_subtermClosed, rightNested_instanceReflecting⟩

/-- Read back: the normal forms of that presentation form a subterm-closed,
instance-reflecting transversal. -/
theorem assoc_normalForms :
    FullyInvariant binTerms AssocEq ∧
      Transversal AssocEq {t | IsNormal (Step binTerms (transversalRules binTerms rightNested_transversal)) t} ∧
      SubtermClosed binTerms
        {t | IsNormal (Step binTerms (transversalRules binTerms rightNested_transversal)) t} ∧
      InstanceReflecting binTerms
        {t | IsNormal (Step binTerms (transversalRules binTerms rightNested_transversal)) t} :=
  normalForms_of_presentation assoc_transversalRules_presentation

end Binary

#print axioms exists_presentation_iff
#print axioms presentation_of_transversal
#print axioms normalForms_of_presentation
#print axioms Binary.commEq_no_transversal
#print axioms Binary.commEq_no_presentation
#print axioms Binary.assoc_presentation

end Mettapedia.Logic.Relation.SchematicPresentation
