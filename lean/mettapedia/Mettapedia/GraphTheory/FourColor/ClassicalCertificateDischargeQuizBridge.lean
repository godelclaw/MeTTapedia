import Mettapedia.GraphTheory.FourColor.ClassicalCertificateQuiz

/-!
# Discharge obstructions as classical catalogue quizzes

Finite `C₂ * C₃` word certificates align each local presentation obstruction
with the quiz generated for a reducible classical configuration.  The root
face period and the singleton sector entries supply all facial arities used by
the certificates.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateDischargeQuizBridge

open ClassicalCertificateCubicWord
open ClassicalCertificateDischargeRuleBoundData
open ClassicalCertificatePresentationPattern
open ClassicalCertificateQuiz
open ClassicalCertificateRotationHubProfile
open GoertzelV24FaceDualConnectedness

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Direct word certificate for the `cf003` quiz inside obstruction 02. -/
def obstruction02Certificate : List VisitMatch :=
  [⟨1, 6, 13, -2⟩,
    ⟨sectorObservationWord 1 .spoke, 5, 0, 0⟩,
    ⟨sectorObservationWord 0 .spoke, 5, 0, 0⟩,
    ⟨sectorObservationWord 1 .hat, 5, 1, 0⟩,
    ⟨sectorObservationWord 4 .spoke, 5, 0, -1⟩,
    ⟨sectorObservationWord 3 .spoke, 5, 0, -1⟩,
    ⟨sectorObservationWord 4 .hat, 5, 1, -1⟩]

theorem obstruction02Certificate_check :
    wordCertificateChecker 6
      (cf003.wordVisits (node⁻¹ * edge)) obstruction02Certificate = true := by
  rfl

/-- Direct word certificate for the `cf001` quiz inside obstruction 00. -/
def obstruction00Certificate : List VisitMatch :=
  [⟨sectorObservationWord 0 .spoke, 5, 1, 0⟩,
    ⟨sectorObservationWord 4 .spoke, 5, -1, -1⟩,
    ⟨1, 5, 10, -2⟩,
    ⟨sectorObservationWord 3 .spoke, 5, 0, -1⟩]

theorem obstruction00Certificate_check :
    wordCertificateChecker 5
      (cf001.wordVisits node⁻¹) obstruction00Certificate = true := by
  rfl

/-- Direct reflected-word certificate for the `cf006` quiz inside
obstruction 01. -/
def obstruction01Certificate : List VisitMatch :=
  [⟨sectorObservationWord 4 .spoke, 6, 0, -1⟩,
    ⟨sectorObservationWord 3 .spoke, 5, 0, -1⟩,
    ⟨sectorObservationWord 4 .hat, 5, 1, -1⟩,
    ⟨sectorObservationWord 1 .spoke, 5, 0, -1⟩,
    ⟨sectorObservationWord 0 .spoke, 5, 0, -1⟩,
    ⟨sectorObservationWord 1 .hat, 5, 1, -1⟩,
    ⟨1, 6, 16, -3⟩]

theorem obstruction01Certificate_check :
    wordCertificateChecker 6
      (cf006Mirror.wordVisits qstepL) obstruction01Certificate = true := by
  rfl

/-- Direct word certificate for the `cf009` quiz inside obstruction 03. -/
def obstruction03Certificate : List VisitMatch :=
  [⟨sectorObservationWord 0 .spoke, 6, 0, 0⟩,
    ⟨sectorObservationWord 4 .spoke, 6, 0, -1⟩,
    ⟨sectorObservationWord 3 .spoke, 5, 0, -1⟩,
    ⟨sectorObservationWord 4 .hat, 5, 1, -1⟩,
    ⟨1, 6, 12, -2⟩,
    ⟨sectorObservationWord 1 .spoke, 5, 1, 0⟩,
    ⟨sectorObservationWord 1 .hat, 5, 1, 0⟩]

theorem obstruction03Certificate_check :
    wordCertificateChecker 6
      (cf009.wordVisits edge) obstruction03Certificate = true := by
  rfl

/-- Direct word certificate for the `cf006` quiz inside obstruction 04. -/
def obstruction04Certificate : List VisitMatch :=
  [⟨sectorObservationWord 0 .spoke, 6, 0, 0⟩,
    ⟨1, 6, 12, -2⟩,
    ⟨sectorObservationWord 1 .spoke, 5, 1, 0⟩,
    ⟨sectorObservationWord 3 .spoke, 5, 0, 0⟩,
    ⟨sectorObservationWord 4 .spoke, 5, 1, 0⟩,
    ⟨sectorObservationWord 4 .hat, 5, 1, 0⟩,
    ⟨sectorObservationWord 1 .hat, 5, 1, 0⟩]

theorem obstruction04Certificate_check :
    wordCertificateChecker 6
      (cf006.wordVisits edge) obstruction04Certificate = true := by
  rfl

/-- Direct word certificate shared by the two `cf024` obstructions. -/
def cf024DirectCertificate : List VisitMatch :=
  [⟨1, 7, 14, -2⟩,
    ⟨sectorObservationWord 0 .spoke, 5, 0, 0⟩,
    ⟨sectorObservationWord 6 .spoke, 5, 0, -1⟩,
    ⟨sectorObservationWord 5 .spoke, 5, 0, -1⟩,
    ⟨sectorObservationWord 4 .spoke, 5, 0, -1⟩]

theorem cf024DirectCertificate_check :
    wordCertificateChecker 7
      (cf024.wordVisits 1) cf024DirectCertificate = true := by
  rfl

/-- Direct word certificate for the `cf139` quiz inside obstruction 07. -/
def obstruction07Certificate : List VisitMatch :=
  [⟨sectorObservationWord 2 .spoke, 7, 0, 0⟩,
    ⟨sectorObservationWord 1 .spoke, 6, 0, 0⟩,
    ⟨sectorObservationWord 0 .spoke, 5, 0, 0⟩,
    ⟨sectorObservationWord 6 .spoke, 5, 0, -1⟩,
    ⟨1, 7, 9, -1⟩,
    ⟨sectorObservationWord 3 .spoke, 6, 1, 0⟩,
    ⟨sectorObservationWord 3 .hat, 5, 1, 0⟩]

theorem obstruction07Certificate_check :
    wordCertificateChecker 7
      (cf139.wordVisits (sectorObservationWord 2 .spoke))
        obstruction07Certificate = true := by
  rfl

/-- Direct word certificate for the `cf182` quiz inside obstruction 08. -/
def obstruction08Certificate : List VisitMatch :=
  [⟨sectorObservationWord 2 .spoke, 7, 0, 0⟩,
    ⟨sectorObservationWord 1 .spoke, 6, 0, 0⟩,
    ⟨sectorObservationWord 0 .spoke, 6, 0, 0⟩,
    ⟨sectorObservationWord 6 .spoke, 5, 0, -1⟩,
    ⟨sectorObservationWord 5 .spoke, 5, 0, -1⟩,
    ⟨1, 7, 16, -2⟩,
    ⟨sectorObservationWord 3 .spoke, 6, 1, 0⟩,
    ⟨sectorObservationWord 3 .hat, 5, 1, 0⟩]

theorem obstruction08Certificate_check :
    wordCertificateChecker 7
      (cf182.wordVisits (sectorObservationWord 2 .spoke))
        obstruction08Certificate = true := by
  rfl

/-- Obstruction 02 contains a fitting copy of the `cf003` catalogue quiz. -/
theorem obstruction02_forces_cf003
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hfits : Pattern.Fits (hubProfile RS root) obstruction02) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf003 := by
  have hcard : (RS.faceOrbit root).card = 6 := by
    simpa [obstruction02] using hfits.length_eq
  have hhub :
      faceArity RS (act RS hcubic hrotation 1 root) = 6 := by
    simpa [faceArity, act] using hcard
  have hs0 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 0 .spoke 5
        (by omega) (by simp [obstruction02]) (by omega)
          (by simp [obstruction02, Sector.rangeAt])
  have hs1 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 1 .spoke 5
        (by omega) (by simp [obstruction02]) (by omega)
          (by simp [obstruction02, Sector.rangeAt])
  have hh1 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 1 .hat 5
        (by omega) (by simp [obstruction02]) (by omega)
          (by simp [obstruction02, Sector.rangeAt])
  have hs3 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 3 .spoke 5
        (by omega) (by simp [obstruction02]) (by omega)
          (by simp [obstruction02, Sector.rangeAt])
  have hs4 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .spoke 5
        (by omega) (by simp [obstruction02]) (by omega)
          (by simp [obstruction02, Sector.rangeAt])
  have hh4 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .hat 5
        (by omega) (by simp [obstruction02]) (by omega)
          (by simp [obstruction02, Sector.rangeAt])
  let anchor := node⁻¹ * edge
  refine ⟨act RS hcubic hrotation anchor root, ?_⟩
  apply quizFits_of_wordCertificate RS hcubic hrotation root 6 hcard
    anchor cf003 obstruction02Certificate obstruction02Certificate_check
  intro certificate hcertificate
  simp only [obstruction02Certificate, List.mem_cons, List.not_mem_nil,
    or_false] at hcertificate
  rcases hcertificate with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hhub
  · exact hs1
  · exact hs0
  · exact hh1
  · exact hs4
  · exact hs3
  · exact hh4

/-- Obstruction 00 contains a fitting copy of the `cf001` catalogue quiz,
certified entirely in the universal cubic word algebra. -/
theorem obstruction00_forces_cf001_word
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hfits : Pattern.Fits (hubProfile RS root) obstruction00) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf001 := by
  have hcard : (RS.faceOrbit root).card = 5 := by
    simpa [obstruction00] using hfits.length_eq
  have hhub :
      faceArity RS (act RS hcubic hrotation 1 root) = 5 := by
    simpa [faceArity, act] using hcard
  have hs0 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 0 .spoke 5
        (by omega) (by simp [obstruction00]) (by omega)
          (by simp [obstruction00, Sector.rangeAt])
  have hs3 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 3 .spoke 5
        (by omega) (by simp [obstruction00]) (by omega)
          (by simp [obstruction00, Sector.rangeAt])
  have hs4 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .spoke 5
        (by omega) (by simp [obstruction00]) (by omega)
          (by simp [obstruction00, Sector.rangeAt])
  let anchor := node⁻¹
  refine ⟨act RS hcubic hrotation anchor root, ?_⟩
  apply quizFits_of_wordCertificate RS hcubic hrotation root 5 hcard
    anchor cf001 obstruction00Certificate obstruction00Certificate_check
  intro certificate hcertificate
  simp only [obstruction00Certificate, List.mem_cons, List.not_mem_nil,
    or_false] at hcertificate
  rcases hcertificate with rfl | rfl | rfl | rfl
  · exact hs0
  · exact hs4
  · exact hhub
  · exact hs3

/-- Obstruction 03 contains a fitting copy of the `cf009` catalogue quiz. -/
theorem obstruction03_forces_cf009
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hfits : Pattern.Fits (hubProfile RS root) obstruction03) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf009 := by
  have hcard : (RS.faceOrbit root).card = 6 := by
    simpa [obstruction03] using hfits.length_eq
  have hhub :
      faceArity RS (act RS hcubic hrotation 1 root) = 6 := by
    simpa [faceArity, act] using hcard
  have hs0 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 0 .spoke 6
        (by omega) (by simp [obstruction03]) (by omega)
          (by simp [obstruction03, Sector.rangeAt])
  have hs1 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 1 .spoke 5
        (by omega) (by simp [obstruction03]) (by omega)
          (by simp [obstruction03, Sector.rangeAt])
  have hh1 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 1 .hat 5
        (by omega) (by simp [obstruction03]) (by omega)
          (by simp [obstruction03, Sector.rangeAt])
  have hs3 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 3 .spoke 5
        (by omega) (by simp [obstruction03]) (by omega)
          (by simp [obstruction03, Sector.rangeAt])
  have hs4 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .spoke 6
        (by omega) (by simp [obstruction03]) (by omega)
          (by simp [obstruction03, Sector.rangeAt])
  have hh4 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .hat 5
        (by omega) (by simp [obstruction03]) (by omega)
          (by simp [obstruction03, Sector.rangeAt])
  let anchor := edge
  refine ⟨act RS hcubic hrotation anchor root, ?_⟩
  apply quizFits_of_wordCertificate RS hcubic hrotation root 6 hcard
    anchor cf009 obstruction03Certificate obstruction03Certificate_check
  intro certificate hcertificate
  simp only [obstruction03Certificate, List.mem_cons, List.not_mem_nil,
    or_false] at hcertificate
  rcases hcertificate with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs0
  · exact hs4
  · exact hs3
  · exact hh4
  · exact hhub
  · exact hs1
  · exact hh1

/-- Obstruction 04 contains a fitting copy of the `cf006` catalogue quiz. -/
theorem obstruction04_forces_cf006
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hfits : Pattern.Fits (hubProfile RS root) obstruction04) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf006 := by
  have hcard : (RS.faceOrbit root).card = 6 := by
    simpa [obstruction04] using hfits.length_eq
  have hhub :
      faceArity RS (act RS hcubic hrotation 1 root) = 6 := by
    simpa [faceArity, act] using hcard
  have hs0 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 0 .spoke 6
        (by omega) (by simp [obstruction04]) (by omega)
          (by simp [obstruction04, Sector.rangeAt])
  have hs1 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 1 .spoke 5
        (by omega) (by simp [obstruction04]) (by omega)
          (by simp [obstruction04, Sector.rangeAt])
  have hh1 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 1 .hat 5
        (by omega) (by simp [obstruction04]) (by omega)
          (by simp [obstruction04, Sector.rangeAt])
  have hs3 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 3 .spoke 5
        (by omega) (by simp [obstruction04]) (by omega)
          (by simp [obstruction04, Sector.rangeAt])
  have hs4 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .spoke 5
        (by omega) (by simp [obstruction04]) (by omega)
          (by simp [obstruction04, Sector.rangeAt])
  have hh4 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .hat 5
        (by omega) (by simp [obstruction04]) (by omega)
          (by simp [obstruction04, Sector.rangeAt])
  let anchor := edge
  refine ⟨act RS hcubic hrotation anchor root, ?_⟩
  apply quizFits_of_wordCertificate RS hcubic hrotation root 6 hcard
    anchor cf006 obstruction04Certificate obstruction04Certificate_check
  intro certificate hcertificate
  simp only [obstruction04Certificate, List.mem_cons, List.not_mem_nil,
    or_false] at hcertificate
  rcases hcertificate with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs0
  · exact hhub
  · exact hs1
  · exact hs3
  · exact hs4
  · exact hh4
  · exact hh1

/-- Four fixed pentagonal spoke words around a seven-face are sufficient for
the direct `cf024` quiz certificate. -/
theorem forces_cf024_of_direct_words
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hcard : (RS.faceOrbit root).card = 7)
    (hs0 : faceArity RS
      (act RS hcubic hrotation (sectorObservationWord 0 .spoke) root) = 5)
    (hs4 : faceArity RS
      (act RS hcubic hrotation (sectorObservationWord 4 .spoke) root) = 5)
    (hs5 : faceArity RS
      (act RS hcubic hrotation (sectorObservationWord 5 .spoke) root) = 5)
    (hs6 : faceArity RS
      (act RS hcubic hrotation (sectorObservationWord 6 .spoke) root) = 5) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf024 := by
  have hhub :
      faceArity RS (act RS hcubic hrotation 1 root) = 7 := by
    simpa [faceArity, act] using hcard
  refine ⟨act RS hcubic hrotation 1 root, ?_⟩
  apply quizFits_of_wordCertificate RS hcubic hrotation root 7 hcard
    1 cf024 cf024DirectCertificate cf024DirectCertificate_check
  intro certificate hcertificate
  simp only [cf024DirectCertificate, List.mem_cons, List.not_mem_nil,
    or_false] at hcertificate
  rcases hcertificate with rfl | rfl | rfl | rfl | rfl
  · exact hhub
  · exact hs0
  · exact hs6
  · exact hs5
  · exact hs4

/-- Obstruction 05 contains a fitting copy of the `cf024` catalogue quiz. -/
theorem obstruction05_forces_cf024
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hfits : Pattern.Fits (hubProfile RS root) obstruction05) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf024 := by
  have hcard : (RS.faceOrbit root).card = 7 := by
    simpa [obstruction05] using hfits.length_eq
  apply forces_cf024_of_direct_words RS hcubic hrotation root hcard
  · exact Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 0 .spoke 5
        (by omega) (by simp [obstruction05]) (by omega)
          (by simp [obstruction05, Sector.rangeAt])
  · exact Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .spoke 5
        (by omega) (by simp [obstruction05]) (by omega)
          (by simp [obstruction05, Sector.rangeAt])
  · exact Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 5 .spoke 5
        (by omega) (by simp [obstruction05]) (by omega)
          (by simp [obstruction05, Sector.rangeAt])
  · exact Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 6 .spoke 5
        (by omega) (by simp [obstruction05]) (by omega)
          (by simp [obstruction05, Sector.rangeAt])

/-- Obstruction 06 contains a fitting copy of the `cf024` catalogue quiz. -/
theorem obstruction06_forces_cf024
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hfits : Pattern.Fits (hubProfile RS root) obstruction06) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf024 := by
  have hcard : (RS.faceOrbit root).card = 7 := by
    simpa [obstruction06] using hfits.length_eq
  apply forces_cf024_of_direct_words RS hcubic hrotation root hcard
  · exact Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 0 .spoke 5
        (by omega) (by simp [obstruction06]) (by omega)
          (by simp [obstruction06, Sector.rangeAt])
  · exact Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .spoke 5
        (by omega) (by simp [obstruction06]) (by omega)
          (by simp [obstruction06, Sector.rangeAt])
  · exact Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 5 .spoke 5
        (by omega) (by simp [obstruction06]) (by omega)
          (by simp [obstruction06, Sector.rangeAt])
  · exact Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 6 .spoke 5
        (by omega) (by simp [obstruction06]) (by omega)
          (by simp [obstruction06, Sector.rangeAt])

/-- Obstruction 07 contains a fitting copy of the `cf139` catalogue quiz. -/
theorem obstruction07_forces_cf139
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hfits : Pattern.Fits (hubProfile RS root) obstruction07) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf139 := by
  have hcard : (RS.faceOrbit root).card = 7 := by
    simpa [obstruction07] using hfits.length_eq
  have hhub :
      faceArity RS (act RS hcubic hrotation 1 root) = 7 := by
    simpa [faceArity, act] using hcard
  have hs0 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 0 .spoke 5
        (by omega) (by simp [obstruction07]) (by omega)
          (by simp [obstruction07, Sector.rangeAt])
  have hs1 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 1 .spoke 6
        (by omega) (by simp [obstruction07]) (by omega)
          (by simp [obstruction07, Sector.rangeAt])
  have hs2 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 2 .spoke 7
        (by omega) (by simp [obstruction07]) (by omega)
          (by simp [obstruction07, Sector.rangeAt])
  have hs3 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 3 .spoke 6
        (by omega) (by simp [obstruction07]) (by omega)
          (by simp [obstruction07, Sector.rangeAt])
  have hh3 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 3 .hat 5
        (by omega) (by simp [obstruction07]) (by omega)
          (by simp [obstruction07, Sector.rangeAt])
  have hs6 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 6 .spoke 5
        (by omega) (by simp [obstruction07]) (by omega)
          (by simp [obstruction07, Sector.rangeAt])
  let anchor := sectorObservationWord 2 .spoke
  refine ⟨act RS hcubic hrotation anchor root, ?_⟩
  apply quizFits_of_wordCertificate RS hcubic hrotation root 7 hcard
    anchor cf139 obstruction07Certificate obstruction07Certificate_check
  intro certificate hcertificate
  simp only [obstruction07Certificate, List.mem_cons, List.not_mem_nil,
    or_false] at hcertificate
  rcases hcertificate with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs2
  · exact hs1
  · exact hs0
  · exact hs6
  · exact hhub
  · exact hs3
  · exact hh3

/-- Obstruction 01 contains the reflected fitting quiz for catalogue
configuration `cf006`. -/
theorem obstruction01_forces_cf006Mirror
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hfits : Pattern.Fits (hubProfile RS root) obstruction01) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf006Mirror := by
  have hcard : (RS.faceOrbit root).card = 6 := by
    simpa [obstruction01] using hfits.length_eq
  have hhub :
      faceArity RS (act RS hcubic hrotation 1 root) = 6 := by
    simpa [faceArity, act] using hcard
  have hs0 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 0 .spoke 5
        (by omega) (by simp [obstruction01]) (by omega)
          (by simp [obstruction01, Sector.rangeAt])
  have hs1 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 1 .spoke 5
        (by omega) (by simp [obstruction01]) (by omega)
          (by simp [obstruction01, Sector.rangeAt])
  have hh1 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 1 .hat 5
        (by omega) (by simp [obstruction01]) (by omega)
          (by simp [obstruction01, Sector.rangeAt])
  have hs3 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 3 .spoke 5
        (by omega) (by simp [obstruction01]) (by omega)
          (by simp [obstruction01, Sector.rangeAt])
  have hs4 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .spoke 6
        (by omega) (by simp [obstruction01]) (by omega)
          (by simp [obstruction01, Sector.rangeAt])
  have hh4 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 4 .hat 5
        (by omega) (by simp [obstruction01]) (by omega)
          (by simp [obstruction01, Sector.rangeAt])
  let anchor := qstepL
  refine ⟨act RS hcubic hrotation anchor root, ?_⟩
  apply quizFits_of_wordCertificate RS hcubic hrotation root 6 hcard
    anchor cf006Mirror obstruction01Certificate
      obstruction01Certificate_check
  intro certificate hcertificate
  simp only [obstruction01Certificate, List.mem_cons, List.not_mem_nil,
    or_false] at hcertificate
  rcases hcertificate with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs4
  · exact hs3
  · exact hh4
  · exact hs1
  · exact hs0
  · exact hh1
  · exact hhub

/-- Obstruction 08 contains a fitting copy of the alternate reducible
catalogue configuration `cf182`. -/
theorem obstruction08_forces_cf182
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (root : RS.D)
    (hfits : Pattern.Fits (hubProfile RS root) obstruction08) :
    ∃ dart : RS.D, Quiz.Fits RS dart cf182 := by
  have hcard : (RS.faceOrbit root).card = 7 := by
    simpa [obstruction08] using hfits.length_eq
  have hhub :
      faceArity RS (act RS hcubic hrotation 1 root) = 7 := by
    simpa [faceArity, act] using hcard
  have hs0 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 0 .spoke 6
        (by omega) (by simp [obstruction08]) (by omega)
          (by simp [obstruction08, Sector.rangeAt])
  have hs1 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 1 .spoke 6
        (by omega) (by simp [obstruction08]) (by omega)
          (by simp [obstruction08, Sector.rangeAt])
  have hs2 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 2 .spoke 7
        (by omega) (by simp [obstruction08]) (by omega)
          (by simp [obstruction08, Sector.rangeAt])
  have hs3 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 3 .spoke 6
        (by omega) (by simp [obstruction08]) (by omega)
          (by simp [obstruction08, Sector.rangeAt])
  have hh3 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 3 .hat 5
        (by omega) (by simp [obstruction08]) (by omega)
          (by simp [obstruction08, Sector.rangeAt])
  have hs5 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 5 .spoke 5
        (by omega) (by simp [obstruction08]) (by omega)
          (by simp [obstruction08, Sector.rangeAt])
  have hs6 :=
    Pattern.Fits.sectorObservationWord_arity_of_singleton
      RS hcubic hrotation root hfits 6 .spoke 5
        (by omega) (by simp [obstruction08]) (by omega)
          (by simp [obstruction08, Sector.rangeAt])
  let anchor := sectorObservationWord 2 .spoke
  refine ⟨act RS hcubic hrotation anchor root, ?_⟩
  apply quizFits_of_wordCertificate RS hcubic hrotation root 7 hcard
    anchor cf182 obstruction08Certificate obstruction08Certificate_check
  intro certificate hcertificate
  simp only [obstruction08Certificate, List.mem_cons, List.not_mem_nil,
    or_false] at hcertificate
  rcases hcertificate with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs2
  · exact hs1
  · exact hs0
  · exact hs6
  · exact hs5
  · exact hhub
  · exact hs3
  · exact hh3

end

end ClassicalCertificateDischargeQuizBridge

end Mettapedia.GraphTheory.FourColor
