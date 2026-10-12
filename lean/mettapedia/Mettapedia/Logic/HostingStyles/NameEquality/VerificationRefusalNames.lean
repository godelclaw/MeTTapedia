import Mettapedia.Logic.HostingStyles.NameEquality.KernelNames

/-!
# One refused verification, run with names as constants

Declarations that state a theorem as a second axiom, against a specification
that has one axiom: the admission alone admits them, and the specification
refuses them.

With names in letters the refusal takes 2569 steps of the table of 497 rules;
that count is a measurement, and its run is not replayed.  In the table with
names as constants, over the test of names, **451 steps** take the call of the
verification to the reading of the refusal, replayed in the kernel
(`verificationNames_refusal_replays`); twenty-two of them are tests of two
names (`verificationRefusalTraceNames_parts`).  So the candidate takes exactly
451 transitions from the run of the verification to the run of the refusal
(`verificationNames_refusal_run_steps`), and with the general theorem the
replayed run gives what the kernel's function returns: nothing
(`secondAxiomDeclarations_refused`).

Positive: the development that proves the theorem is verified, in 788 steps
(`verificationNames_instance_replays`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (boolean natural)
open Mettapedia.GSLT.Dedukti (RewriteRule Step Reduces)
open Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
  (encodeAdmission encodeTheoryResult)
open Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
  (encodeEntries encodeEntry encodeProofDeclarations encodeProofDeclaration)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (atomsReduce atomsReduceTheory closedAtom program_reaches)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## The specification and the declarations as data -/

/-- The specification without the theorem as data, written out. -/
theorem axiomSpecification_data :
    encodeEntries axiomSpecification =
      .list [.list [.sym "MM0:SpecSort", natural 0,
          .list [.sym "MM0:Sort", .sym "False", .sym "False", .sym "True", .sym "False"]],
        .list [.sym "MM0:SpecTerm", natural 0,
          .list [.sym "MM0:TermDecl", .list [], natural 0, .list []]],
        .list [.sym "MM0:SpecAxiom", natural 0,
          .list [.sym "MM0:Theorem", .list [], .list [], .expr [.sym "MM0:Term", natural 0]]]] := by
  simp [axiomSpecification, encodeEntries, encodeEntry, boolean,
    Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration.encodeSort,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDeclaration,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeContext,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDependencies,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeNaturals,
    Mettapedia.Languages.MM0.Presentation.ComputationalProof.encodeTheorem,
    Mettapedia.Languages.MM0.Presentation.ComputationalArguments.encodeExpressions,
    Mettapedia.Languages.MM0.Presentation.encode]

/-- The declarations with a second axiom as data, written out. -/
theorem secondAxiomDeclarations_data :
    encodeProofDeclarations secondAxiomDeclarations =
      .list [.list [.sym "MM0:ProofDeclaration", .sym "False",
          .list [.sym "MM0:AdmitSort", natural 0,
            .list [.sym "MM0:Sort", .sym "False", .sym "False", .sym "True", .sym "False"]]],
        .list [.sym "MM0:ProofDeclaration", .sym "False",
          .list [.sym "MM0:AdmitTerm", natural 0,
            .list [.sym "MM0:TermDecl", .list [], natural 0, .list []]]],
        .list [.sym "MM0:ProofDeclaration", .sym "False",
          .list [.sym "MM0:AdmitAxiom", natural 0,
            .list [.sym "MM0:Theorem", .list [], .list [],
              .expr [.sym "MM0:Term", natural 0]]]],
        .list [.sym "MM0:ProofDeclaration", .sym "False",
          .list [.sym "MM0:AdmitAxiom", natural 1,
            .list [.sym "MM0:Theorem", .list [], .list [],
              .expr [.sym "MM0:Term", natural 0]]]]] := by
  simp [secondAxiomDeclarations, encodeProofDeclarations, encodeProofDeclaration,
    encodeAdmission, boolean,
    Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration.encodeSort,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDeclaration,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeContext,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDependencies,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeNaturals,
    Mettapedia.Languages.MM0.Presentation.ComputationalProof.encodeTheorem,
    Mettapedia.Languages.MM0.Presentation.ComputationalArguments.encodeExpressions,
    Mettapedia.Languages.MM0.Presentation.encode]

/-! ## The trace -/

set_option maxRecDepth 1000000 in
/-- The trace of the refused verification: 451 steps. -/
def verificationRefusalTraceNames : List (Nat × Nat) :=
  [(1, 380), (13, 375), (109, 419), (13, 377), (109, 370), (877, 365), (7021, 419), (877, 369),
    (7021, 391), (228205, 442), (228205, 448), (1801069, 442), (1801069, 448), (14383981, 438),
    (14383981, 0), (29064045, 448), (230390637, 444), (465271661, 448), (3686497133, 444),
    (7444593517, 445), (465271661, 483), (29064045, 483), (1801069, 483), (3636077, 448),
    (28801901, 442), (28801901, 448), (230128493, 438), (230128493, 0), (465009517, 448),
    (3686234989, 444), (7444331373, 448), (58983938925, 444), (119113481069, 445), (7444331373,
    483), (465009517, 483), (28801901, 483), (58162029, 445), (3636077, 483), (228205, 483),
    (7021, 392), (7021, 393), (7021, 437), (7021, 442), (7021, 448), (56173, 440), (449389, 426),
    (908141, 479), (56173, 483), (113517, 448), (899949, 442), (899949, 448), (7191405, 438),
    (7191405, 0), (14531437, 448), (115194733, 438), (115194733, 0), (232635245, 448),
    (1843247981, 438), (1843247981, 0), (3722296173, 448), (29492099949, 438), (29492099949, 0),
    (59556871021, 448), (471873731437, 438), (471873731437, 0), (952910068589, 445), (59556871021,
    483), (3722296173, 483), (232635245, 483), (14531437, 483), (899949, 483), (1817453, 445),
    (113517, 483), (7021, 483), (877, 367), (109, 372), (877, 354), (7021, 348), (7021, 345),
    (56173, 131), (449389, 418), (56173, 132), (7021, 346), (877, 356), (877, 357), (227181, 420),
    (109, 374), (13, 379), (13, 375), (109, 419), (13, 377), (109, 370), (877, 365), (7021, 419),
    (877, 369), (7021, 391), (228205, 442), (228205, 448), (1801069, 442), (1801069, 448),
    (14383981, 438), (14383981, 0), (29064045, 448), (230390637, 444), (465271661, 448),
    (3686497133, 444), (7444593517, 445), (465271661, 483), (29064045, 483), (1801069, 484),
    (3636077, 448), (28801901, 442), (28801901, 448), (230128493, 438), (230128493, 0),
    (465009517, 448), (3686234989, 444), (7444331373, 448), (58983938925, 444), (119113481069,
    445), (7444331373, 483), (465009517, 483), (28801901, 484), (58162029, 445), (3636077, 484),
    (228205, 484), (7021, 394), (228205, 442), (228205, 448), (1801069, 442), (1801069, 448),
    (14383981, 438), (14383981, 0), (29064045, 448), (230390637, 444), (465271661, 448),
    (3686497133, 444), (7444593517, 445), (465271661, 483), (29064045, 483), (1801069, 483),
    (3636077, 448), (28801901, 442), (28801901, 448), (230128493, 438), (230128493, 0),
    (465009517, 448), (3686234989, 444), (7444331373, 448), (58983938925, 444), (119113481069,
    445), (7444331373, 483), (465009517, 483), (28801901, 483), (58162029, 445), (3636077, 483),
    (228205, 483), (7021, 395), (7021, 396), (7021, 437), (7021, 442), (7021, 448), (56173, 440),
    (449389, 426), (908141, 479), (56173, 483), (113517, 448), (899949, 442), (899949, 448),
    (7191405, 438), (7191405, 0), (14531437, 448), (115194733, 442), (115194733, 445), (232635245,
    448), (1843247981, 440), (14728149869, 426), (29760535405, 479), (1843247981, 483),
    (3722296173, 448), (29492099949, 442), (29492099949, 445), (59556871021, 445), (3722296173,
    483), (232635245, 483), (14531437, 483), (899949, 483), (1817453, 445), (113517, 483), (7021,
    483), (877, 367), (109, 372), (877, 354), (7021, 349), (56173, 345), (449389, 131), (3595117,
    418), (449389, 132), (56173, 346), (113517, 259), (899949, 258), (899949, 253), (7191405,
    418), (899949, 254), (113517, 261), (899949, 242), (7191405, 131), (57523053, 419), (7191405,
    133), (57523053, 425), (57523053, 426), (7191405, 134), (899949, 246), (899949, 230), (113517,
    263), (113517, 237), (899949, 418), (113517, 238), (7021, 231), (877, 356), (877, 358),
    (456557, 420), (109, 374), (13, 379), (13, 375), (109, 419), (13, 377), (109, 370), (877,
    365), (7021, 419), (877, 369), (7021, 391), (228205, 442), (228205, 448), (1801069, 442),
    (1801069, 448), (14383981, 438), (14383981, 0), (29064045, 448), (230390637, 444), (465271661,
    448), (3686497133, 444), (7444593517, 445), (465271661, 483), (29064045, 483), (1801069, 484),
    (3636077, 448), (28801901, 442), (28801901, 448), (230128493, 438), (230128493, 0),
    (465009517, 448), (3686234989, 444), (7444331373, 448), (58983938925, 444), (119113481069,
    445), (7444331373, 483), (465009517, 483), (28801901, 484), (58162029, 445), (3636077, 484),
    (228205, 484), (7021, 394), (228205, 442), (228205, 448), (1801069, 442), (1801069, 448),
    (14383981, 438), (14383981, 0), (29064045, 448), (230390637, 444), (465271661, 448),
    (3686497133, 444), (7444593517, 445), (465271661, 483), (29064045, 483), (1801069, 484),
    (3636077, 448), (28801901, 442), (28801901, 448), (230128493, 438), (230128493, 0),
    (465009517, 448), (3686234989, 444), (7444331373, 448), (58983938925, 444), (119113481069,
    445), (7444331373, 483), (465009517, 483), (28801901, 484), (58162029, 445), (3636077, 484),
    (228205, 484), (7021, 397), (228205, 442), (228205, 448), (1801069, 442), (1801069, 448),
    (14383981, 438), (14383981, 0), (29064045, 448), (230390637, 444), (465271661, 448),
    (3686497133, 444), (7444593517, 447), (465271661, 483), (29064045, 483), (1801069, 484),
    (3636077, 448), (28801901, 442), (28801901, 448), (230128493, 438), (230128493, 0),
    (465009517, 448), (3686234989, 444), (7444331373, 448), (58983938925, 444), (119113481069,
    447), (7444331373, 483), (465009517, 483), (28801901, 484), (58162029, 445), (3636077, 484),
    (228205, 484), (7021, 400), (228205, 442), (228205, 448), (1801069, 442), (1801069, 448),
    (14383981, 438), (14383981, 0), (29064045, 448), (230390637, 444), (465271661, 448),
    (3686497133, 444), (7444593517, 445), (465271661, 483), (29064045, 483), (1801069, 483),
    (3636077, 448), (28801901, 442), (28801901, 448), (230128493, 438), (230128493, 0),
    (465009517, 448), (3686234989, 444), (7444331373, 448), (58983938925, 444), (119113481069,
    445), (7444331373, 483), (465009517, 483), (28801901, 483), (58162029, 445), (3636077, 483),
    (228205, 483), (7021, 401), (7021, 402), (7021, 437), (7021, 442), (7021, 448), (56173, 440),
    (449389, 426), (908141, 479), (56173, 483), (113517, 448), (899949, 442), (899949, 448),
    (7191405, 438), (7191405, 0), (14531437, 448), (115194733, 442), (115194733, 445), (232635245,
    448), (1843247981, 442), (1843247981, 445), (3722296173, 448), (29492099949, 441),
    (29492099949, 448), (235650530157, 438), (235650530157, 0), (476168698733, 448),
    (3774703582061, 440), (30162982648685, 426), (60949308226413, 479), (3774703582061, 483),
    (7622994279277, 445), (476168698733, 483), (29492099949, 483), (59556871021, 445),
    (3722296173, 483), (232635245, 483), (14531437, 483), (899949, 483), (1817453, 445), (113517,
    483), (7021, 483), (877, 367), (109, 372), (877, 354), (7021, 351), (56173, 345), (449389,
    131), (3595117, 418), (449389, 132), (56173, 346), (113517, 279), (899949, 258), (899949,
    253), (7191405, 418), (899949, 254), (113517, 281), (899949, 274), (7191405, 418), (899949,
    275), (1817453, 269), (14400365, 12), (115063661, 6), (920370029, 419), (115063661, 8),
    (920370029, 425), (920370029, 426), (115063661, 9), (14400365, 18), (1817453, 271), (14400365,
    418), (1817453, 272), (1817453, 242), (14400365, 131), (115063661, 419), (14400365, 133),
    (115063661, 425), (115063661, 426), (14400365, 134), (1817453, 247), (113517, 231), (7021,
    231), (877, 356), (877, 360), (1832813, 420), (109, 374), (13, 379), (13, 375), (109, 419),
    (13, 377), (109, 370), (877, 365), (7021, 418), (877, 368), (109, 371), (13, 378), (1, 381)]

set_option maxRecDepth 100000 in
/-- The refused verification: 451 steps, of which twenty-two by the family. -/
theorem verificationRefusalTraceNames_parts :
    verificationRefusalTraceNames.length = 451 ∧
      (verificationRefusalTraceNames.countP fun step => partOf 384 33 step.2 = .family) =
        22 := by
  decide +kernel

/-! ## The refusal, replayed -/

set_option maxRecDepth 100000 in
/-- **Negative**: 451 steps take the call of the verification of the
declarations with a second axiom to the reading of the refusal. -/
theorem verificationNames_refusal_replays :
    replayNamesCoded verificationTableNames verificationRefusalTraceNames
        (verificationCall axiomSpecification secondAxiomDeclarations) =
      some (datum constantSpelling (encodeTheoryResult none)) := by
  rw [verificationCall, axiomSpecification_data, secondAxiomDeclarations_data]
  decide +kernel

/-- **Negative**: the candidate takes exactly 451 transitions from the run of
the verification of the declarations with a second axiom to the run of the
refusal. -/
theorem verificationNames_refusal_run_steps :
    atomsReduceTheory.Steps 451 (verificationRunNames axiomSpecification secondAxiomDeclarations)
      (verifiedRunNames axiomSpecification secondAxiomDeclarations none) := by
  have steps := replayNamesCoded_stepsIn verificationNames_stored
    verificationNames_refusal_replays
  rw [verificationRefusalTraceNames_parts.1] at steps
  exact localRun_steps verificationNames_stores.runnable (namesFor_covers _ _)
    (namesFor_within _ _) steps

/-- **What the kernel's function returns, from the replayed run**: the run of
the verification reaches the run of the refusal by the 451 replayed steps, so
the public entry of the kernel returns nothing for the declarations with a
second axiom. -/
theorem secondAxiomDeclarations_refused :
    Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? axiomSpecification
        secondAxiomDeclarations =
      none :=
  (verificationNames_run_iff axiomSpecification secondAxiomDeclarations none).mp
    (program_reaches (localTable_runnable verificationNames_stores.runnable _)
      ((reduces_withNames_iff_local verificationNames_stores.runnable.2 (namesFor_covers _ _)
        (namesFor_within _ _)).mp
        (replayNamesCoded_stepsIn verificationNames_stored
          verificationNames_refusal_replays).reduces))

#print axioms verificationRefusalTraceNames_parts
#print axioms verificationNames_refusal_replays
#print axioms verificationNames_refusal_run_steps
#print axioms secondAxiomDeclarations_refused

end Mettapedia.Logic.HostingStyles.NameEquality
