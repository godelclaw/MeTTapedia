import Mettapedia.Logic.HostingStyles.NameEquality.KernelNames

/-!
# The verification of one development against its specification, run with names as constants

The development: a provable sort, a constant of it, an axiom asserting the
constant, and a theorem restating the axiom, proved by applying it.  Its
specification states the four declarations.

With names in letters the verification takes 4360 steps of the table of 497
rules; that count is a measurement, and its run is not replayed.  In the table
with names as constants, over the test of names, **788 steps** take the call
of the verification to the reading of the encoded theory, and **the whole run
is replayed in the kernel** (`verificationNames_instance_replays`): the public
entry of MM0's kernel, on a whole development against its specification, run
by stored rules and the test of names.  With the general theorem the replayed
run gives what the kernel's function returns (`restatedDevelopment_verified`).

Where the steps go (`verificationTraceNames_parts`).  The number of an entry
of the trace names a part of the table, and the rule at that number is a rule
of that part (`rule_mem_partRules`, with the sizes
`verificationNames_partSizes`):

| steps | by |
|---|---|
| 174 | rules of equations of the unordered heads |
| 20 | ordered rules: the trials of the three ordered heads |
| 67 | rules of the shared host: list view and arithmetic |
| 491 | rules that compare data without comparing names |
| 36 | the family: one step for each test of two names |

So the candidate takes exactly 788 transitions from the run of the
verification to the run of the theory, in the space that stores the table and
the rules of the family for the names of the call
(`verificationNames_instance_run_steps`).  The counts are those of one
strategy, leftmost innermost.

The refused verification is replayed in its own module, for the memory that a
replay takes: `verificationNames_refusal_replays`.
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

/-- The specification of the development as data, written out. -/
theorem restatedSpecification_data :
    encodeEntries restatedSpecification =
      .list [.list [.sym "MM0:SpecSort", natural 0,
          .list [.sym "MM0:Sort", .sym "False", .sym "False", .sym "True", .sym "False"]],
        .list [.sym "MM0:SpecTerm", natural 0,
          .list [.sym "MM0:TermDecl", .list [], natural 0, .list []]],
        .list [.sym "MM0:SpecAxiom", natural 0,
          .list [.sym "MM0:Theorem", .list [], .list [], .expr [.sym "MM0:Term", natural 0]]],
        .list [.sym "MM0:SpecTheorem", natural 1,
          .list [.sym "MM0:Theorem", .list [], .list [], .expr [.sym "MM0:Term", natural 0]]]] := by
  simp [restatedSpecification, encodeEntries, encodeEntry, boolean,
    Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration.encodeSort,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDeclaration,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeContext,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDependencies,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeNaturals,
    Mettapedia.Languages.MM0.Presentation.ComputationalProof.encodeTheorem,
    Mettapedia.Languages.MM0.Presentation.ComputationalArguments.encodeExpressions,
    Mettapedia.Languages.MM0.Presentation.encode]

/-- The declarations of the development as data, written out. -/
theorem restatedDeclarations_data :
    encodeProofDeclarations restatedDeclarations =
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
          .list [.sym "MM0:AdmitTheorem", natural 1,
            .list [.sym "MM0:Theorem", .list [], .list [], .expr [.sym "MM0:Term", natural 0]],
            .list [], .list [.sym "MM0:TheoremApp", natural 0, .list [], .list []]]]] := by
  simp [restatedDeclarations, restatedDevelopment, encodeProofDeclarations,
    encodeProofDeclaration, encodeAdmission, boolean,
    Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration.encodeSort,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDeclaration,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeContext,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDependencies,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeNaturals,
    Mettapedia.Languages.MM0.Presentation.ComputationalProof.encodeTheorem,
    Mettapedia.Languages.MM0.Presentation.ComputationalProof.encodeProof,
    Mettapedia.Languages.MM0.Presentation.ComputationalArguments.encodeExpressions,
    Mettapedia.Languages.MM0.Presentation.encode]

/-! ## The trace -/

set_option maxRecDepth 1000000 in
/-- **The trace of the verification of the development against its
specification**: 788 steps. -/
def verificationTraceNames : List (Nat × Nat) :=
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
    (13, 377), (109, 370), (877, 365), (7021, 419), (877, 369), (7021, 391), (228205, 442),
    (228205, 448), (1801069, 442), (1801069, 448), (14383981, 438), (14383981, 0), (29064045,
    448), (230390637, 444), (465271661, 448), (3686497133, 444), (7444593517, 445), (465271661,
    483), (29064045, 483), (1801069, 484), (3636077, 448), (28801901, 442), (28801901, 448),
    (230128493, 438), (230128493, 0), (465009517, 448), (3686234989, 444), (7444331373, 448),
    (58983938925, 444), (119113481069, 446), (7444331373, 483), (465009517, 483), (28801901, 484),
    (58162029, 445), (3636077, 484), (228205, 484), (7021, 394), (228205, 442), (228205, 448),
    (1801069, 442), (1801069, 448), (14383981, 438), (14383981, 0), (29064045, 448), (230390637,
    444), (465271661, 448), (3686497133, 444), (7444593517, 445), (465271661, 483), (29064045,
    483), (1801069, 484), (3636077, 448), (28801901, 442), (28801901, 448), (230128493, 438),
    (230128493, 0), (465009517, 448), (3686234989, 444), (7444331373, 448), (58983938925, 444),
    (119113481069, 446), (7444331373, 483), (465009517, 483), (28801901, 484), (58162029, 445),
    (3636077, 484), (228205, 484), (7021, 397), (228205, 442), (228205, 448), (1801069, 442),
    (1801069, 448), (14383981, 438), (14383981, 0), (29064045, 448), (230390637, 444), (465271661,
    448), (3686497133, 444), (7444593517, 447), (465271661, 483), (29064045, 483), (1801069, 484),
    (3636077, 448), (28801901, 442), (28801901, 448), (230128493, 438), (230128493, 0),
    (465009517, 448), (3686234989, 444), (7444331373, 448), (58983938925, 444), (119113481069,
    448), (943747201901, 444), (1905819876205, 446), (119113481069, 483), (7444331373, 483),
    (465009517, 483), (28801901, 484), (58162029, 445), (3636077, 484), (228205, 484), (7021,
    400), (228205, 442), (228205, 448), (1801069, 442), (1801069, 448), (14383981, 438),
    (14383981, 0), (29064045, 448), (230390637, 444), (465271661, 448), (3686497133, 444),
    (7444593517, 445), (465271661, 483), (29064045, 483), (1801069, 484), (3636077, 448),
    (28801901, 442), (28801901, 448), (230128493, 438), (230128493, 0), (465009517, 448),
    (3686234989, 444), (7444331373, 448), (58983938925, 444), (119113481069, 446), (7444331373,
    483), (465009517, 483), (28801901, 484), (58162029, 445), (3636077, 484), (228205, 484),
    (7021, 403), (228205, 442), (228205, 448), (1801069, 442), (1801069, 448), (14383981, 438),
    (14383981, 0), (29064045, 448), (230390637, 444), (465271661, 448), (3686497133, 444),
    (7444593517, 445), (465271661, 483), (29064045, 483), (1801069, 483), (3636077, 448),
    (28801901, 442), (28801901, 448), (230128493, 438), (230128493, 0), (465009517, 448),
    (3686234989, 444), (7444331373, 448), (58983938925, 444), (119113481069, 448), (943747201901,
    444), (1905819876205, 448), (15099959409517, 444), (30493122198381, 445), (1905819876205,
    483), (119113481069, 483), (7444331373, 483), (465009517, 483), (28801901, 483), (58162029,
    445), (3636077, 483), (228205, 483), (7021, 404), (7021, 405), (7021, 437), (7021, 442),
    (7021, 448), (56173, 440), (449389, 429), (449389, 426), (908141, 479), (56173, 483), (113517,
    448), (899949, 442), (899949, 448), (7191405, 438), (7191405, 0), (14531437, 448), (115194733,
    442), (115194733, 445), (232635245, 448), (1843247981, 442), (1843247981, 445), (3722296173,
    448), (29492099949, 441), (29492099949, 448), (235650530157, 438), (235650530157, 0),
    (476168698733, 448), (3774703582061, 440), (30162982648685, 426), (60949308226413, 479),
    (3774703582061, 483), (7622994279277, 445), (476168698733, 483), (29492099949, 483),
    (59556871021, 445), (3722296173, 483), (232635245, 483), (14531437, 483), (899949, 483),
    (1817453, 445), (113517, 483), (7021, 483), (877, 367), (109, 372), (877, 354), (7021, 352),
    (3595117, 345), (28760941, 131), (230087533, 419), (28760941, 133), (230087533, 425),
    (230087533, 428), (28760941, 135), (28760941, 131), (230087533, 418), (28760941, 132),
    (3595117, 346), (7265133, 279), (57596781, 258), (57596781, 253), (460249965, 418), (57596781,
    254), (7265133, 281), (57596781, 274), (460249965, 418), (57596781, 275), (116317037, 269),
    (921623405, 12), (7364074349, 6), (58903681901, 419), (7364074349, 8), (58903681901, 425),
    (58903681901, 426), (7364074349, 9), (921623405, 18), (116317037, 271), (921623405, 418),
    (116317037, 272), (116317037, 242), (921623405, 131), (7364074349, 419), (921623405, 133),
    (7364074349, 425), (7364074349, 426), (921623405, 134), (116317037, 247), (7265133, 231),
    (449389, 231), (908141, 264), (7199597, 418), (908141, 265), (56173, 231), (113517, 353),
    (116374381, 332), (921680749, 418), (116374381, 333), (7322477, 38), (57654125, 418),
    (7322477, 39), (113517, 228), (899949, 205), (7191405, 131), (57523053, 419), (7191405, 133),
    (57523053, 425), (57523053, 426), (7191405, 134), (899949, 208), (7191405, 196), (57523053,
    98), (460176237, 73), (3681401709, 418), (7439498093, 418), (460176237, 74), (57523053, 100),
    (929938285, 80), (7372389229, 418), (14888581997, 418), (929938285, 81), (57523053, 101),
    (57523053, 93), (460176237, 418), (57523053, 94), (7191405, 198), (233683821, 113),
    (1844296557, 418), (233683821, 114), (7191405, 199), (57523053, 189), (460176237, 418),
    (57523053, 190), (7191405, 201), (57523053, 103), (7191405, 203), (899949, 210), (7191405,
    221), (57523053, 418), (7191405, 222), (899949, 212), (7191405, 437), (7191405, 442),
    (7191405, 445), (899949, 214), (113517, 437), (113517, 441), (113517, 448), (899949, 438),
    (899949, 0), (1817453, 448), (14400365, 441), (14400365, 448), (115063661, 438), (115063661,
    0), (232504173, 448), (1843116909, 440), (14728018797, 426), (29760404333, 479), (1843116909,
    483), (3722165101, 445), (232504173, 483), (14400365, 483), (29080429, 445), (1817453, 483),
    (113517, 483), (7021, 231), (877, 356), (877, 361), (1832813, 420), (109, 374), (13, 379),
    (13, 375), (109, 418), (13, 376), (1, 382), (13, 418), (1, 383)]

set_option maxRecDepth 100000 in
/-- **Where the steps of the verification go**: 788 steps, of which 174 by
rules of equations, 20 by ordered rules, 67 by rules of the shared host, 491
by rules that compare data, and 36 by the family.  The table begins with 384
rules of equations and thirty-three ordered rules
(`verificationNames_partSizes`). -/
theorem verificationTraceNames_parts :
    verificationTraceNames.length = 788 ∧
      (verificationTraceNames.countP fun step => partOf 384 33 step.2 = .equations) = 174 ∧
      (verificationTraceNames.countP fun step => partOf 384 33 step.2 = .ordered) = 20 ∧
      (verificationTraceNames.countP fun step => partOf 384 33 step.2 = .sharedHost) = 67 ∧
      (verificationTraceNames.countP fun step => partOf 384 33 step.2 = .comparison) = 491 ∧
      (verificationTraceNames.countP fun step => partOf 384 33 step.2 = .family) = 36 := by
  decide +kernel

/-! ## The verification, replayed -/

set_option maxRecDepth 100000 in
/-- **Replaying the trace in the table with the family**: 788 steps take the
call of the verification of the development against its specification to the
reading of its encoded theory. -/
theorem verificationNames_instance_replays :
    replayNamesCoded verificationTableNames verificationTraceNames
        (verificationCall restatedSpecification restatedDeclarations) =
      some (datum constantSpelling (encodeTheoryResult (some restatedTheory))) := by
  rw [verificationCall, restatedSpecification_data, restatedDeclarations_data,
    restatedTheory_data]
  decide +kernel

/-- **A reduction of exactly 788 steps**, in the theory of the table with the
family, from the call of the verification to the reading of the theory. -/
theorem verificationNames_instance_steps :
    StepsIn (withNames verificationTableNames) 788
      (verificationCall restatedSpecification restatedDeclarations)
      (datum constantSpelling (encodeTheoryResult (some restatedTheory))) := by
  have steps := replayNamesCoded_stepsIn verificationNames_stored
    verificationNames_instance_replays
  rwa [verificationTraceNames_parts.1] at steps

/-- **The candidate takes exactly 788 transitions** from the run of the
verification of the development against its specification to the run of its
theory, in the space that stores the table and the rules of the family for the
names of the call. -/
theorem verificationNames_instance_run_steps :
    atomsReduceTheory.Steps 788 (verificationRunNames restatedSpecification restatedDeclarations)
      (verifiedRunNames restatedSpecification restatedDeclarations (some restatedTheory)) :=
  localRun_steps verificationNames_stores.runnable (namesFor_covers _ _) (namesFor_within _ _)
    verificationNames_instance_steps

/-- **What the kernel's function returns, from the replayed run**: the run of
the verification reaches the run of the theory by the 788 replayed steps, so
the public entry of the kernel returns that theory for the development. -/
theorem restatedDevelopment_verified :
    Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? restatedSpecification
        restatedDeclarations =
      some restatedTheory :=
  (verificationNames_run_iff restatedSpecification restatedDeclarations (some restatedTheory)).mp
    (program_reaches (localTable_runnable verificationNames_stores.runnable _)
      ((reduces_withNames_iff_local verificationNames_stores.runnable.2 (namesFor_covers _ _)
        (namesFor_within _ _)).mp verificationNames_instance_steps.reduces))

#print axioms verificationTraceNames_parts
#print axioms verificationNames_instance_replays
#print axioms verificationNames_instance_steps
#print axioms verificationNames_instance_run_steps
#print axioms restatedDevelopment_verified

end Mettapedia.Logic.HostingStyles.NameEquality
