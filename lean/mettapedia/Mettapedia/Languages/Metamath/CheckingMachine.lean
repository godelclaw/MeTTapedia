import Mettapedia.Languages.Metamath.InferenceNormalFoldReflection
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.GSLT.LanguageDef.CertificateGSLTBorrowedCursor
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable

/-!
# Checking realizations of an admitted Metamath snapshot

Source reflection of normal-label execution is independent of this adapter.
The projected calculus also admits shared proof graphs, retained source-address
checking and portable presentation loading, under its original projection laws.
-/

namespace Mettapedia.Languages.Metamath.CheckingMachine

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceNormalFoldReflection

/-- Under the original snapshot conditions, native normal-label provability
is exactly a closed arrow of the existing proof category. No checking-machine
or source-navigation observation enters this correspondence. -/
theorem classifyingArrow_iff_acceptedNormalLabels
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.val)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[]) :
    Nonempty ((⟨[]⟩ : CertificateGSLT.ClassifyingContext target) ⟶
        ⟨[proves (encodeFormula formula)]⟩) ↔
      ∃ labels : List String,
        labels.foldlM (fun state label => db.stepNormal state label) base =
          .ok (base.push formula.toRuntime) := by
  let comparison := CertificateGSLT.ClassifyingContext.closedDerivationEquiv
    target (proves (encodeFormula formula))
  constructor
  · rintro ⟨arrow⟩
    exact (nonempty_provesDerivation_iff_exists_acceptedNormalLabels
      db projection target base formula hprojection hproject hbaseStack).mp
        ⟨comparison.symm arrow⟩
  · intro accepted
    obtain ⟨proof⟩ := (nonempty_provesDerivation_iff_exists_acceptedNormalLabels
      db projection target base formula hprojection hproject hbaseStack).mpr accepted
    exact ⟨comparison proof⟩

/-! ## The admitted snapshot on the common checking interface -/

/-- Source-address checking retains the actual projected calculus. The
projection and native execution comparisons below remain explicit obligations
of the chosen database snapshot; a name or digest cannot replace them. -/
def checkingObject (target : ValidatedCalculusLanguageDef)
    (source : CertificateGSLT.BorrowedCursor.Source) :=
  CertificateGSLT.BorrowedCursor.checkingObject target source

/-- Projecting for a fresh target prevents a newly claimed theorem from being
used as its own source assertion. The module retains all admitted declarations;
the absence check does not claim parser-prefix provenance. -/
def moduleForFreshTarget? (db : RuntimeDB) (targetLabel : String) : Option String :=
  (projectForFreshTarget? db targetLabel).map fun target =>
    ModuleFormat.Portable.renderCalculus target.val

theorem moduleForFreshTarget_read (db : RuntimeDB) (targetLabel : String)
    (target : ValidatedCalculusLanguageDef)
    (projected : projectForFreshTarget? db targetLabel = some target) :
    (moduleForFreshTarget? db targetLabel).bind ModuleFormat.Portable.readValidatedCalculus? =
      some target := by
  simp [moduleForFreshTarget?, projected]

/-- Native Metamath label execution and common checked graphs have the same
theorem image under the established source-projection conditions. Ordered
normal-label execution remains Metamath's original `DB.stepNormal`. -/
theorem graph_iff_acceptedNormalLabels
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.val)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[]) :
    (∃ (nodes : List (Mettapedia.Logic.DerivationGraph.Node
        Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
        (CertificateGSLT.BorrowedCursor.AdmittedInstance target) Nat))
      (cache : Array Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (root : Nat),
      Mettapedia.Logic.DerivationGraph.replay
        (CertificateGSLT.BorrowedCursor.presentation target).ruleWitness nodes = some cache ∧
        cache[root]? = some (proves (encodeFormula formula))) ↔
      ∃ labels : List String,
        labels.foldlM (fun state label => db.stepNormal state label) base =
          .ok (base.push formula.toRuntime) :=
  (CertificateGSLT.BorrowedCursor.authored_source_and_graph
    ⟨target⟩ (proves (encodeFormula formula))).2.symm.trans
      (nonempty_provesDerivation_iff_exists_acceptedNormalLabels
        db projection target base formula hprojection hproject hbaseStack)

/-- A retained common-cursor root supplies a proof executable by the original
normal Metamath verifier, under the same database, frame and target formula. -/
theorem checked_root_has_normalLabels
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef) (base : RuntimeProofState)
    (formula : ConstantHeadedFormula)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.val)
    (hproject : projectPrefix? db = some projection)
    (hbaseStack : base.stack = #[])
    (source : CertificateGSLT.BorrowedCursor.Source)
    (cursor : CertificateGSLT.BorrowedCursor.Cursor target source) (address : Nat)
    (found : Mettapedia.Logic.DerivationGraph.BorrowedCursor.rootAt cursor.state address =
      some (proves (encodeFormula formula))) :
    ∃ labels : List String,
      labels.foldlM (fun state label => db.stepNormal state label) base =
        .ok (base.push formula.toRuntime) :=
  (nonempty_provesDerivation_iff_exists_acceptedNormalLabels
    db projection target base formula hprojection hproject hbaseStack).mp
      (CertificateGSLT.BorrowedCursor.checked_root_source_derivation
        target source cursor address _ found)

end Mettapedia.Languages.Metamath.CheckingMachine
