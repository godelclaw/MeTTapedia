import Mettapedia.InformationTheory.ShannonEntropy.Faddeev
import Mettapedia.InformationTheory.ShannonEntropy.ShannonKhinchin
import InformationTheory.ShannonEntropy.Equivalence

/-!
# Entropy axiom systems through their canonical interpretation

The semantic records remain independently defined. Their reversible interpretations
compose with the canonical function-preserving equivalence. Existence is a separate
corollary; counting clauses does not establish axiomatic minimality.
-/
namespace Mettapedia.InformationTheory

def faddeevShannonKhinchinEquiv : FaddeevEntropy ≃ ShannonKhinchinEntropy :=
  FaddeevEntropy.equivStandalone.trans
    (_root_.InformationTheory.faddeevShannonKhinchinEquiv.trans ShannonKhinchinEntropy.equivStandalone.symm)

@[simp] theorem faddeevShannonKhinchinEquiv_H (E : FaddeevEntropy) {n : ℕ} (p : ProbVec n) :
    (faddeevShannonKhinchinEquiv E).H p = E.H p := rfl
@[simp] theorem faddeevShannonKhinchinEquiv_symm_H (E : ShannonKhinchinEntropy) {n : ℕ} (p : ProbVec n) :
    (faddeevShannonKhinchinEquiv.symm E).H p = E.H p := rfl

theorem faddeev_implies_shannonKhinchin (E : FaddeevEntropy) :
    ∃ E' : ShannonKhinchinEntropy, ∀ (n : ℕ) (p : ProbVec n), E'.H p = E.H p :=
  ⟨faddeevShannonKhinchinEquiv E, fun _ _ => rfl⟩
theorem shannonKhinchin_implies_faddeev (E : ShannonKhinchinEntropy) :
    ∃ E' : FaddeevEntropy, ∀ (n : ℕ) (p : ProbVec n), E'.H p = E.H p :=
  ⟨faddeevShannonKhinchinEquiv.symm E, fun _ _ => rfl⟩

theorem faddeev_iff_shannonKhinchin : Nonempty FaddeevEntropy ↔ Nonempty ShannonKhinchinEntropy :=
  faddeevShannonKhinchinEquiv.nonempty_congr
end Mettapedia.InformationTheory
