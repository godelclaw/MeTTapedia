import Mettapedia.Logic.WorldModel.Indexed.Contracts
import Mettapedia.PLN.WorldModel.WorldModelCalculus

/-!
# The existing query comparisons are graded identity arrows

`WMQueryEq`, `WMEvidenceLE` and `WMViewEq` compare two questions of one world
model.  Read each question as a single-question world model over the one-world
base (`reading`).  Then the three comparisons are exactly the statements that
the identity state map from the first reading to the second is graded by the
exact contract, by evidence dominance, and by the view
(`wmQueryEq_iff_graded`, `wmEvidenceLE_iff_graded`, `wmViewEq_iff_viewGraded`).
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed.ContractBridges

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open FixedQuery CountContracts

/-- Binary evidence as the single answer of the one-world base. -/
noncomputable def evidenceProfiles : Pointᵒᵖ ⥤ AddCommMonCat :=
  (Functor.const _).obj (AddCommMonCat.of BinaryEvidence)

variable {State Query : Type} [EvidenceType State] [BinaryWorldModel State Query]

/-- The single-question reading of a binary world model. -/
noncomputable def reading (q : Query) : Over (evidenceProfiles.obj (op pt)) :=
  Over.mk (AddCommMonCat.ofHom (BinaryWorldModel.evidenceHomAt (State := State) (Query := Query) q) :
    AddCommMonCat.of State ⟶ evidenceProfiles.obj (op pt))

/-- Evidence dominance: the delivered evidence is at least the required one. -/
noncomputable def evidenceDominance : ContractSystem evidenceProfiles where
  rel _ x y := (show BinaryEvidence from y) ≤ (show BinaryEvidence from x)
  restrict _ _ _ h := h

/-- Query equality is exactness of the identity between the two readings. -/
theorem wmQueryEq_iff_graded (q₁ q₂ : Query) :
    WMQueryEq (State := State) (Query := Query) q₁ q₂ ↔
      Graded evidenceProfiles ContractSystem.exact (𝟙 pt) (reading q₁) (reading q₂)
        (𝟙 (AddCommMonCat.of State)) :=
  ⟨fun h W => (h W).symm, fun h W => (h W).symm⟩

/-- Evidence dominance between queries is dominance-grading of the identity. -/
theorem wmEvidenceLE_iff_graded (q₁ q₂ : Query) :
    WMEvidenceLE (State := State) (Query := Query) q₁ q₂ ↔
      Graded evidenceProfiles evidenceDominance (𝟙 pt) (reading q₁) (reading q₂)
        (𝟙 (AddCommMonCat.of State)) :=
  Iff.rfl

/-- View equality between queries is view-grading of the identity. -/
theorem wmViewEq_iff_viewGraded {α : Type} (view : BinaryEvidence → α) (q₁ q₂ : Query) :
    WMViewEq (State := State) (Query := Query) view q₁ q₂ ↔
      ViewGraded (P := evidenceProfiles) (b := pt) (fun e => view e) (𝟙 pt) (reading q₁) (reading q₂)
        (𝟙 (AddCommMonCat.of State)) :=
  ⟨fun h W => (h W).symm, fun h W => (h W).symm⟩

end Mettapedia.Logic.WorldModel.Indexed.ContractBridges
