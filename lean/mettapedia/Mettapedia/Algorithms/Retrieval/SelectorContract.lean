import Mathlib.Data.Finset.Card

/-!
# View identity and guarantees for reusable candidate selectors

A selector denotes row/occurrence identities in one source, revision, layout
and projection. Symbolic bindings are separate payloads; a row set alone does
not encode multiplicity or substitutions. These are model obligations for a
future shared access-method boundary, not a claim that all runtime indexes
already implement that boundary.

Exact and complete-superset guarantees compose for intersection and union.
Difference is different: completeness requires the right operand to be exact
(or at least have no false positives). A superset's complement is unsound.
Approximate candidates cannot be admitted as complete without another proof.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Retrieval.SelectorContract

structure View where
  source : Nat
  revision : Nat
  layout : Nat
  projection : Nat
  profile : Nat
  deriving DecidableEq

inductive Guarantee where
  | exact
  | complete
  | approximate
  deriving DecidableEq

def Respects {I : Type*} (g : Guarantee) (meaning candidates : Finset I) : Prop :=
  match g with
  | .exact => candidates = meaning
  | .complete => meaning ⊆ candidates
  | .approximate => True

structure Selection (I : Type*) where
  view : View
  guarantee : Guarantee
  rows : Finset I

def admit {I : Type*} (expected : View) (selection : Selection I) : Option (Finset I) :=
  if selection.view = expected then some selection.rows else none

theorem incompatible_view_refused {I : Type*} (expected : View) (selection : Selection I)
    (h : selection.view ≠ expected) : admit expected selection = none := by
  simp [admit, h]

theorem layout_is_part_of_identity (source revision projection profile : Nat) :
    ({source, revision, layout := 0, projection, profile} : View) ≠
      {source, revision, layout := 1, projection, profile} := by
  intro h
  have hl := congrArg View.layout h
  contradiction

/-- A caller requiring completeness must also check the declared guarantee.
The provider still owes `Respects`; a label alone is not a proof. -/
def admitComplete {I : Type*} (expected : View) (selection : Selection I) :
    Option (Finset I) :=
  match selection.guarantee with
  | .approximate => none
  | .exact | .complete => admit expected selection

theorem approximate_complete_request_refused {I : Type*} (expected : View)
    (selection : Selection I) (h : selection.guarantee = .approximate) :
    admitComplete expected selection = none := by
  simp [admitComplete, h]

theorem admitted_rows_identical {I : Type*} (expected : View) (selection : Selection I)
    (rows : Finset I) (h : admit expected selection = some rows) :
    rows = selection.rows := by
  unfold admit at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

/-- Complete admission, together with a sound provider contract, cannot lose
an answer. Approximate providers do not satisfy the admission premise. -/
theorem admitted_complete_covers {I : Type*} (expected : View)
    (selection : Selection I) (meaning rows : Finset I)
    (valid : Respects selection.guarantee meaning selection.rows)
    (accepted : admitComplete expected selection = some rows) : meaning ⊆ rows := by
  cases h : selection.guarantee with
  | approximate => simp [admitComplete, h] at accepted
  | exact =>
    have ha : admit expected selection = some rows := by simpa [admitComplete, h] using accepted
    have hv : selection.rows = meaning := by simpa [Respects, h] using valid
    rw [admitted_rows_identical expected selection rows ha, hv]
  | complete =>
    have ha : admit expected selection = some rows := by simpa [admitComplete, h] using accepted
    rw [admitted_rows_identical expected selection rows ha]
    simpa [Respects, h] using valid

theorem exact_implies_complete {I : Type*} {meaning candidates : Finset I}
    (h : Respects .exact meaning candidates) : Respects .complete meaning candidates := by
  change candidates = meaning at h
  change meaning ⊆ candidates
  rw [h]

section Sets

variable {I : Type*} [DecidableEq I]

theorem intersect_complete {a b ca cb : Finset I}
    (ha : Respects .complete a ca) (hb : Respects .complete b cb) :
    Respects .complete (a ∩ b) (ca ∩ cb) := by
  intro i hi
  rcases Finset.mem_inter.mp hi with ⟨hia, hib⟩
  exact Finset.mem_inter.mpr ⟨ha hia, hb hib⟩

theorem union_complete {a b ca cb : Finset I}
    (ha : Respects .complete a ca) (hb : Respects .complete b cb) :
    Respects .complete (a ∪ b) (ca ∪ cb) := by
  intro i hi
  rcases Finset.mem_union.mp hi with hia | hib
  · exact Finset.mem_union_left _ (ha hia)
  · exact Finset.mem_union_right _ (hb hib)

theorem difference_complete {a b ca cb : Finset I}
    (ha : Respects .complete a ca) (hb : Respects .exact b cb) :
    Respects .complete (a \ b) (ca \ cb) := by
  intro i hi
  rcases Finset.mem_sdiff.mp hi with ⟨hia, hib⟩
  change cb = b at hb
  rw [hb]
  exact Finset.mem_sdiff.mpr ⟨ha hia, hib⟩

theorem superset_difference_loses_answer :
    Respects .complete (∅ : Finset Nat) {0} ∧
      ¬ Respects .complete ({0} \ ∅ : Finset Nat) ({0} \ {0}) := by
  simp [Respects]

theorem approximate_does_not_imply_complete :
    Respects .approximate ({0} : Finset Nat) ∅ ∧
      ¬ Respects .complete ({0} : Finset Nat) ∅ := by
  simp [Respects]

end Sets

/-- Transport from another index domain requires a no-false-dismissal map.
Representational similarity, alone, is not a completeness certificate. -/
theorem transport_complete {I A Q R : Type*}
    (project : I → A) (translate : Q → R)
    (meaning : Q → I → Prop) (abstract : R → A → Prop)
    (candidates : R → A → Prop)
    (soundMap : ∀ q i, meaning q i → abstract (translate q) (project i))
    (soundIndex : ∀ r a, abstract r a → candidates r a) :
    ∀ q i, meaning q i → candidates (translate q) (project i) :=
  fun q i hi => soundIndex _ _ (soundMap q i hi)

theorem transport_composes {I A B Q R S : Type*}
    (first : I → A) (second : A → B) (qfirst : Q → R) (qsecond : R → S)
    (meaning : Q → I → Prop) (middle : R → A → Prop) (last : S → B → Prop)
    (hfirst : ∀ q i, meaning q i → middle (qfirst q) (first i))
    (hsecond : ∀ r a, middle r a → last (qsecond r) (second a)) :
    ∀ q i, meaning q i → last (qsecond (qfirst q)) (second (first i)) :=
  transport_complete first qfirst meaning middle
    (fun r a => last (qsecond r) (second a)) hfirst hsecond

end Mettapedia.Algorithms.Retrieval.SelectorContract
