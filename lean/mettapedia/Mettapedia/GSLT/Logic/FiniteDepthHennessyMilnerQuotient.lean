import Mettapedia.GSLT.Logic.FiniteDepthHennessyMilnerControls

/-!
# Finite observation classes and exact predicate descent

The actual round equivalence defines a quotient of the original state
carrier. Its complete profile reading is injective; finite actual atoms and
labels therefore give finitely many depth-indexed observation classes.

A state predicate descends precisely when it respects the actual round
equivalence. The descended predicate is unique. This does not supply
dependent receipt erasure: the controls identify different original states
while rejecting a readout that recovers their original identity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner.FiniteDepth

universe uAtom uLabel

variable {S : GSLT} (M : System.{uAtom, uLabel} S) (depth : Nat)

def approximationSetoid : Setoid S.Term where
  r := Rounds M depth
  iseqv := ⟨rounds_refl M depth, fun related => rounds_symm M depth related,
    fun before after => rounds_trans M depth before after⟩

abbrev Approximation := Quotient (approximationSetoid M depth)

def quotientReading : Approximation M depth → Profile M.Atom M.Label depth :=
  Quotient.lift (reading M depth) fun _ _ related => reading_eq_of_rounds M depth related

theorem quotientReading_injective : Function.Injective (quotientReading M depth) := by
  intro first second
  refine Quotient.inductionOn₂ first second ?_
  intro before after same
  exact Quotient.sound (rounds_of_reading_eq M depth same)

theorem quotient_eq_iff_rounds (first second : S.Term) :
    (⟦first⟧ : Approximation M depth) = ⟦second⟧ ↔ Rounds M depth first second :=
  Quotient.eq

instance approximation_finite [Finite M.Atom] [Finite M.Label] : Finite (Approximation M depth) :=
  Finite.of_injective (quotientReading M depth) (quotientReading_injective M depth)

def PredicateCompatible (predicate : S.Term → Prop) : Prop :=
  ∀ first second, Rounds M depth first second → (predicate first ↔ predicate second)

def descendPredicate (predicate : S.Term → Prop) (compatible : PredicateCompatible M depth predicate) :
    Approximation M depth → Prop :=
  Quotient.lift predicate fun first second related => propext (compatible first second related)

theorem descendPredicate_readout (predicate : S.Term → Prop)
    (compatible : PredicateCompatible M depth predicate) (term : S.Term) :
    descendPredicate M depth predicate compatible ⟦term⟧ ↔ predicate term := Iff.rfl

theorem predicateDescent_iff (predicate : S.Term → Prop) :
    (∃ descended : Approximation M depth → Prop,
      ∀ term : S.Term, descended ⟦term⟧ ↔ predicate term) ↔ PredicateCompatible M depth predicate := by
  constructor
  · rintro ⟨descended, readout⟩ first second related
    have same : (⟦first⟧ : Approximation M depth) = ⟦second⟧ := Quotient.sound related
    exact (readout first).symm.trans (same ▸ readout second)
  · intro compatible
    exact ⟨descendPredicate M depth predicate compatible, descendPredicate_readout M depth predicate compatible⟩

theorem predicateDescent_unique (predicate : S.Term → Prop)
    (compatible : PredicateCompatible M depth predicate) :
    ∃! descended : Approximation M depth → Prop,
      ∀ term : S.Term, descended ⟦term⟧ ↔ predicate term := by
  refine ⟨descendPredicate M depth predicate compatible,
    descendPredicate_readout M depth predicate compatible, ?_⟩
  intro other reads
  funext value
  refine Quotient.inductionOn value ?_
  intro term
  exact propext (reads term)

theorem formula_predicate_compatible (formula : Formula M.Atom M.Label) (bounded : formula.depth ≤ depth) :
    PredicateCompatible M depth (M.sat formula) :=
  fun _ _ related => sat_iff_of_rounds M formula depth bounded related

def formulaPredicate (formula : Formula M.Atom M.Label) (bounded : formula.depth ≤ depth) :
    Approximation M depth → Prop :=
  descendPredicate M depth (M.sat formula) (formula_predicate_compatible M depth formula bounded)

theorem formulaPredicate_readout (formula : Formula M.Atom M.Label) (bounded : formula.depth ≤ depth)
    (term : S.Term) : formulaPredicate M depth formula bounded ⟦term⟧ ↔ M.sat formula term := Iff.rfl

namespace QuotientControls

open BehavioralCoverControls

theorem infinite_states_have_finite_observation_classes (depth : Nat) :
    Set.Infinite {target | system.act () (.branch false) target} ∧
      Finite (Approximation system depth) :=
  ⟨literal_successors_are_infinite, inferInstance⟩

theorem distinct_originals_have_the_same_class (depth : Nat) :
    State.branch false ≠ .branch true ∧
      (⟦State.branch false⟧ : Approximation system depth) = ⟦State.branch true⟧ :=
  ⟨by decide, Quotient.sound (rounds_of_bisimilar system depth (bisimilar_of_kind_eq rfl))⟩

theorem no_original_state_decoder (depth : Nat) :
    ¬ ∃ decoder : Approximation system depth → State,
      ∀ state : State, decoder ⟦state⟧ = state := by
  rintro ⟨decoder, recovers⟩
  have same := congrArg decoder (distinct_originals_have_the_same_class depth).2
  have impossible : State.branch false = State.branch true :=
    (recovers (.branch false)).symm.trans (same.trans (recovers (.branch true)))
  exact (distinct_originals_have_the_same_class depth).1 impossible

theorem original_identity_predicate_cannot_descend (depth : Nat) :
    ¬ ∃ predicate : Approximation system depth → Prop,
      ∀ state : State, predicate ⟦state⟧ ↔ state = State.branch false := by
  intro descends
  have compatible := (predicateDescent_iff system depth (fun state => state = State.branch false)).mp descends
  have impossible := (compatible (.branch false) (.branch true)
    (rounds_of_bisimilar system depth (bisimilar_of_kind_eq rfl))).mp rfl
  cases impossible

theorem one_additional_round_separates_the_classes :
    (⟦State.branch false⟧ : Approximation system 0) = ⟦State.terminal 0⟧ ∧
      (⟦State.branch false⟧ : Approximation system 1) ≠ ⟦State.terminal 0⟧ := by
  refine ⟨Quotient.sound Controls.InfiniteBranching.depth_zero_cannot_observe_an_enabled_step, ?_⟩
  intro same
  exact Controls.InfiniteBranching.depth_one_observes_the_step
    ((quotient_eq_iff_rounds system 1 _ _).mp same)

end QuotientControls

end Mettapedia.GSLT.HennessyMilner.FiniteDepth
