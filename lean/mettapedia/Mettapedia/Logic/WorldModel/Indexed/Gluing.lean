import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mettapedia.Logic.WorldModel.Indexed.SourceExample
import Mettapedia.PLN.Evidence.PLNJointEvidenceNoGo

/-!
# States across worlds and gluing

**States across worlds.** A presheaf of state monoids with an extraction
natural into the profiles is an object of the slice of presheaves over the
profile functor, `Over P` in `Bᵒᵖ ⥤ AddCommMonCat`.  At each world it gives a
world model (`StatePresheaf.at`), and each restriction of states is a morphism
in the fibre from the reindexed later model to the earlier one
(`StatePresheaf.restrictHom`).  This is the direction of the opfibration over
`Bᵒᵖ`.  Sections of the fibration `worldOf P` go the other way: their state maps
push states forward along arrows.  The two agree when the state maps are
identities, as for the retained record (`recordPresheaf`, `recordHom`).

**Gluing on the source worlds.** Cover a world by sub-worlds whose union is it.
For the per-source questions, which are local to a cover, compatible local
states glue to one state (`glue_perSource`).  For the full questions, which
include the aggregate counts, gluing fails: the states `{a+}` at `{a}` and
`{b+}` at `{b}` agree on the world without sources, and no state has both
local profiles, because the aggregate couples the sources
(`joint_question_does_not_glue`).

**Local completeness.** The local-completeness no-go of the joint-evidence
calculus is the consumer law for a question that is not local to its premises:
the conclusion evidence does not factor through the five local premises
(`linkAC_not_factorsThrough_premises`), and the existing no-go follows from it
(`no_local_complete_deduction_of_law`).
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed

universe vB uB u

section Presheaves

variable {B : Type uB} [Category.{vB} B] {P : Bᵒᵖ ⥤ AddCommMonCat.{u}}

/-- The world model at one world of a presheaf of states over the profiles. -/
def StatePresheaf.at (X : Over P) (b : B) : Over (P.obj (op b)) :=
  Over.mk (X.hom.app (op b))

/-- A restriction of states is a morphism in the fibre over the earlier world,
from the reindexed later model to the earlier model. -/
def StatePresheaf.restrictHom (X : Over P) {b c : B} (f : b ⟶ c) :
    (Over.map (P.map f.op)).obj (StatePresheaf.at X c) ⟶ StatePresheaf.at X b :=
  Over.homMk (X.left.map f.op) (X.hom.naturality f.op)

end Presheaves

namespace Sources

variable {Src : Type} [DecidableEq Src]

/-- The answers of the retained record, natural in the world. -/
def recordAnswers :
    (Functor.const _).obj (AddCommMonCat.of (Records Src)) ⟶ sourceProfiles (Src := Src) where
  app W := AddCommMonCat.ofHom (answer W.unop)
  naturality W W' f := by
    ext m
    funext q
    exact (congrFun (answer_restrict f.unop m) q).symm

/-- The retained record as a presheaf of states: the same records at every
world, answering each world's questions. -/
def recordPresheaf : Over (sourceProfiles (Src := Src)) := Over.mk recordAnswers

/-- The record presheaf at a world is the record model. -/
theorem recordPresheaf_at (W : Finset Src) :
    StatePresheaf.at recordPresheaf W = recordModel W := rfl

/-! ## Gluing per-source questions -/

/-- The per-source answers of a state at a world. -/
def perSource (W : Finset Src) (m : Records Src) : {a // a ∈ W} → Bool → ℕ :=
  fun a sign => m.count (a.1, sign)

/-- For each source of a world, its records, taken from the state of a chosen
owner. -/
noncomputable def gather {ι : Type} (W : Finset Src) (owner : {a // a ∈ W} → ι)
    (states : ι → Records Src) : Records Src :=
  ∑ a ∈ W.attach, (states (owner a)).filter (fun r => r.1 = a.1)

theorem count_gather {ι : Type} (W : Finset Src) (owner : {a // a ∈ W} → ι)
    (states : ι → Records Src) {b : Src} (hb : b ∈ W) (sign : Bool) :
    (gather W owner states).count (b, sign) = (states (owner ⟨b, hb⟩)).count (b, sign) := by
  unfold gather
  rw [Multiset.count_sum']
  simp only [Multiset.count_filter]
  rw [Finset.sum_eq_single ⟨b, hb⟩]
  · simp
  · intro x _ hx
    have : ¬ b = x.1 := fun e => hx (Subtype.ext e.symm)
    simp [this]
  · intro h
    exact absurd (Finset.mem_attach W ⟨b, hb⟩) h

/-- **Gluing for local questions.** If sub-worlds cover `W` and the local states
agree on the per-source questions of every overlap, one state at `W` has every
local per-source profile. -/
theorem glue_perSource {ι : Type} (W : Finset Src) (Ws : ι → Finset Src)
    (inside : ∀ i, Ws i ⊆ W) (cover : ∀ a ∈ W, ∃ i, a ∈ Ws i) (states : ι → Records Src)
    (compatible : ∀ i j, ∀ a, a ∈ Ws i → a ∈ Ws j → ∀ sign,
      (states i).count (a, sign) = (states j).count (a, sign)) :
    ∃ m : Records Src, ∀ i, perSource (Ws i) m = perSource (Ws i) (states i) := by
  let owner : {a // a ∈ W} → ι := fun a => Classical.choose (cover a.1 a.2)
  refine ⟨gather W owner states, fun i => ?_⟩
  funext a sign
  have haW : a.1 ∈ W := inside i a.2
  show (gather W owner states).count (a.1, sign) = (states i).count (a.1, sign)
  rw [count_gather W owner states haW sign]
  exact compatible _ i a.1 (Classical.choose_spec (cover a.1 haW)) a.2 sign

/-- **Gluing fails for a joint question.** The states `{a+}` at `{a}` and `{b+}`
at `{b}` have the same profile at the world without sources, which is their
overlap, and no state has both local profiles: the aggregate count couples
the two sources. -/
theorem joint_question_does_not_glue (a b : Src) (hab : a ≠ b) :
    answer ∅ ({(a, true)} : Records Src) = answer ∅ {(b, true)} ∧
      ¬ ∃ m : Records Src, answer {a} m = answer {a} {(a, true)} ∧
        answer {b} m = answer {b} {(b, true)} := by
  constructor
  · funext q
    cases q with
    | aggregate sign =>
        show (({(a, true)} : Records Src).filter (fun r => r.2 = sign)).card =
          (({(b, true)} : Records Src).filter (fun r => r.2 = sign)).card
        cases sign <;> simp [Multiset.filter_singleton]
    | perSource source mem sign => exact absurd mem (Finset.notMem_empty source)
  · rintro ⟨m, ha, hb⟩
    have countA : m.count (a, true) = 1 := by
      have := congrFun ha (.perSource a (Finset.mem_singleton_self a) true)
      simpa [answer, answerFun] using this
    have countB : m.count (b, true) = 1 := by
      have := congrFun hb (.perSource b (Finset.mem_singleton_self b) true)
      simpa [answer, answerFun] using this
    have total : (m.filter (fun r => r.2 = true)).card = 1 := by
      have := congrFun ha (.aggregate true)
      simpa [answer, answerFun, Multiset.filter_singleton] using this
    obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp total
    have inA : (m.filter (fun r => r.2 = true)).count (a, true) = 1 := by
      rw [Multiset.count_filter, if_pos rfl, countA]
    have inB : (m.filter (fun r => r.2 = true)).count (b, true) = 1 := by
      rw [Multiset.count_filter, if_pos rfl, countB]
    rw [hx, Multiset.count_singleton] at inA inB
    split_ifs at inA inB with h1 h2
    exact hab (congrArg Prod.fst (h1.trans h2.symm))

end Sources

/-! ## Local completeness is the consumer law for a non-local question -/

section LocalCompleteness

open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.PLNJointEvidence
open Mettapedia.PLN.Evidence.PLNJointEvidence.JointEvidence
open Mettapedia.PLN.Evidence.PLNJointEvidenceNoGo
open Mettapedia.PLN.Evidence.PLNJointEvidenceNoGo.Example3

/-- The five local premises of a joint evidence state. -/
noncomputable def premises (E : JointEvidence 3) :
    BinaryEvidence × BinaryEvidence × BinaryEvidence × BinaryEvidence × BinaryEvidence :=
  (propEvidence (n := 3) (E := E) A, propEvidence (n := 3) (E := E) B,
    propEvidence (n := 3) (E := E) C, linkEvidence (n := 3) (E := E) A B,
    linkEvidence (n := 3) (E := E) B C)

/-- The conclusion evidence does not factor through the local premises. -/
theorem linkAC_not_factorsThrough_premises :
    ¬ (fun E : JointEvidence 3 => linkEvidence (n := 3) (E := E) A C).FactorsThrough premises := by
  intro factors
  obtain ⟨hA, hB, hC, hAB, hBC⟩ := premises_agree
  exact conclusion_diff (factors (a := E₁) (b := E₂) (by simp [premises, hA, hB, hC, hAB, hBC]))

/-- The existing local-completeness no-go, derived from the consumer law. -/
theorem no_local_complete_deduction_of_law
    (f : BinaryEvidence → BinaryEvidence → BinaryEvidence → BinaryEvidence → BinaryEvidence →
      BinaryEvidence) :
    ¬ (∀ E : JointEvidence 3,
        f (propEvidence (n := 3) (E := E) A) (propEvidence (n := 3) (E := E) B)
          (propEvidence (n := 3) (E := E) C) (linkEvidence (n := 3) (E := E) A B)
          (linkEvidence (n := 3) (E := E) B C) =
        linkEvidence (n := 3) (E := E) A C) := by
  intro law
  apply linkAC_not_factorsThrough_premises
  intro E E' same
  simp only [premises, Prod.mk.injEq] at same
  obtain ⟨hA, hB, hC, hAB, hBC⟩ := same
  show linkEvidence (n := 3) (E := E) A C = linkEvidence (n := 3) (E := E') A C
  rw [← law E, ← law E', hA, hB, hC, hAB, hBC]

end LocalCompleteness

end Mettapedia.Logic.WorldModel.Indexed
