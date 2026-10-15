import Mettapedia.Logic.HostingStyles.NameEquality.KernelNames

/-!
# The admission of one development, run with names as constants

The development: a provable sort, a constant of it, an axiom asserting the
constant, and a theorem restating the axiom, proved by applying it.

With names in letters its admission takes 343 steps of the table of 453 rules
(`StoredPrograms.admission_instance_replays`).  In the table with names as
constants, over the test of names, **225 steps** take the call of the
admission to the reading of the encoded theory, replayed in the kernel
(`admissionNames_instance_replays`): MM0's kernel admits four declarations and
checks a proof, run by stored rules and the test of names.

Where the steps go (`admissionTraceNames_parts`).  The number of an entry of
the trace names a part of the table, and the rule at that number is a rule of
that part (`rule_mem_partRules`, with the sizes `admissionNames_partSizes`):

| steps | by |
|---|---|
| 148 | rules of equations of the unordered heads |
| 0 | ordered rules |
| 54 | rules of the shared host: list view and arithmetic |
| 21 | rules that compare data without comparing names |
| 2 | the family: one step for each test of two names |

So the candidate takes exactly 225 transitions from the run of the admission
to the run of the theory, in the space that stores the table and the rules of
the family for the names of the call (`admissionNames_instance_run_steps`).
The counts are those of one strategy, leftmost innermost.

Negative: the admission of a term whose sort is not declared is refused in
twenty-six steps, as with names in letters, and none of them is a test of two
names (`admissionNames_refusal_replays`, `admissionRefusalTraceNames_parts`,
`admissionNames_refusal_run_steps`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti (RewriteRule Step Reduces)
open Mettapedia.Languages.MM0.Presentation.ComputationalAdmission (encodeTheoryResult)
open Mettapedia.Logic.HostingStyles.AtomsReduce (atomsReduce atomsReduceTheory closedAtom)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## The traces -/

set_option maxRecDepth 1000000 in
/-- **The trace of the admission of the development**: 225 steps, each the
code of its path and the number of its rule. -/
def admissionTraceNames : List (Nat × Nat) :=
  [(1, 367), (1, 362), (13, 375), (1, 364), (13, 354), (109, 348), (109, 345), (877, 131),
    (7021, 374), (877, 132), (109, 346), (13, 356), (13, 357), (3549, 376), (1, 366), (1, 362),
    (13, 375), (1, 364), (13, 354), (109, 349), (877, 345), (7021, 131), (56173, 374), (7021,
    132), (877, 346), (1773, 259), (14061, 258), (14061, 253), (112365, 374), (14061, 254), (1773,
    261), (14061, 242), (112365, 131), (898797, 375), (112365, 133), (898797, 381), (898797, 382),
    (112365, 134), (14061, 246), (14061, 230), (1773, 263), (1773, 237), (14061, 374), (1773,
    238), (109, 231), (13, 356), (13, 358), (7133, 376), (1, 366), (1, 362), (13, 375), (1, 364),
    (13, 354), (109, 351), (877, 345), (7021, 131), (56173, 374), (7021, 132), (877, 346), (1773,
    279), (14061, 258), (14061, 253), (112365, 374), (14061, 254), (1773, 281), (14061, 274),
    (112365, 374), (14061, 275), (28397, 269), (225005, 12), (1797869, 6), (14380781, 375),
    (1797869, 8), (14380781, 381), (14380781, 382), (1797869, 9), (225005, 18), (28397, 271),
    (225005, 374), (28397, 272), (28397, 242), (225005, 131), (1797869, 375), (225005, 133),
    (1797869, 381), (1797869, 382), (225005, 134), (28397, 247), (1773, 231), (109, 231), (13,
    356), (13, 360), (28637, 376), (1, 366), (1, 362), (13, 375), (1, 364), (13, 354), (109, 352),
    (56173, 345), (449389, 131), (3595117, 375), (449389, 133), (3595117, 381), (3595117, 384),
    (449389, 135), (449389, 131), (3595117, 374), (449389, 132), (56173, 346), (113517, 279),
    (899949, 258), (899949, 253), (7191405, 374), (899949, 254), (113517, 281), (899949, 274),
    (7191405, 374), (899949, 275), (1817453, 269), (14400365, 12), (115063661, 6), (920370029,
    375), (115063661, 8), (920370029, 381), (920370029, 382), (115063661, 9), (14400365, 18),
    (1817453, 271), (14400365, 374), (1817453, 272), (1817453, 242), (14400365, 131), (115063661,
    375), (14400365, 133), (115063661, 381), (115063661, 382), (14400365, 134), (1817453, 247),
    (113517, 231), (7021, 231), (14189, 264), (112493, 374), (14189, 265), (877, 231), (1773,
    353), (1818349, 332), (14401261, 374), (1818349, 333), (114413, 38), (900845, 374), (114413,
    39), (1773, 228), (14061, 205), (112365, 131), (898797, 375), (112365, 133), (898797, 381),
    (898797, 382), (112365, 134), (14061, 208), (112365, 196), (898797, 98), (7190253, 73),
    (57521901, 374), (116242157, 374), (7190253, 74), (898797, 100), (14530285, 80), (115193581,
    374), (232634093, 374), (14530285, 81), (898797, 101), (898797, 93), (7190253, 374), (898797,
    94), (112365, 198), (3651309, 113), (28817133, 374), (3651309, 114), (112365, 199), (898797,
    189), (7190253, 374), (898797, 190), (112365, 201), (898797, 103), (112365, 203), (14061,
    210), (112365, 221), (898797, 374), (112365, 222), (14061, 212), (112365, 393), (112365, 398),
    (112365, 401), (14061, 214), (1773, 393), (1773, 397), (1773, 404), (14061, 394), (14061, 0),
    (28397, 404), (225005, 397), (225005, 404), (1797869, 394), (1797869, 0), (3632877, 404),
    (28798701, 396), (230125293, 382), (465006317, 435), (28798701, 439), (58158829, 401),
    (3632877, 439), (225005, 439), (454381, 401), (28397, 439), (1773, 439), (109, 231), (13,
    356), (13, 361), (28637, 376), (1, 366), (1, 362), (13, 374), (1, 363)]

set_option maxRecDepth 1000000 in
/-- The trace of the refused admission: twenty-six steps. -/
def admissionRefusalTraceNames : List (Nat × Nat) :=
  [(1, 367), (1, 362), (13, 375), (1, 364), (13, 354), (109, 349), (877, 345), (7021, 131),
    (56173, 374), (7021, 132), (877, 346), (1773, 259), (14061, 258), (14061, 253), (112365, 374),
    (14061, 254), (1773, 261), (14061, 242), (112365, 131), (898797, 374), (112365, 132), (14061,
    243), (1773, 262), (109, 231), (13, 355), (1, 365)]

set_option maxRecDepth 100000 in
/-- **Where the steps of the admission go**: 225 steps, of which 148 by rules
of equations, none by an ordered rule, 54 by rules of the shared host, 21 by
rules that compare data, and two by the family.  The table begins with 367
rules of equations and six ordered rules (`admissionNames_partSizes`). -/
theorem admissionTraceNames_parts :
    admissionTraceNames.length = 225 ∧
      (admissionTraceNames.countP fun step => partOf 367 6 step.2 = .equations) = 148 ∧
      (admissionTraceNames.countP fun step => partOf 367 6 step.2 = .ordered) = 0 ∧
      (admissionTraceNames.countP fun step => partOf 367 6 step.2 = .sharedHost) = 54 ∧
      (admissionTraceNames.countP fun step => partOf 367 6 step.2 = .comparison) = 21 ∧
      (admissionTraceNames.countP fun step => partOf 367 6 step.2 = .family) = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The refused admission: twenty-six steps, none of them by the family. -/
theorem admissionRefusalTraceNames_parts :
    admissionRefusalTraceNames.length = 26 ∧
      (admissionRefusalTraceNames.countP fun step => partOf 367 6 step.2 = .family) = 0 := by
  decide +kernel

/-! ## The admission, replayed -/

set_option maxRecDepth 100000 in
/-- **Replaying the trace in the table with the family**: 225 steps take the
call of the admission of the development to the reading of its encoded
theory. -/
theorem admissionNames_instance_replays :
    replayNamesCoded admissionTableNames admissionTraceNames
        (admissionCall restatedDevelopment) =
      some (datum constantSpelling (encodeTheoryResult (some restatedTheory))) := by
  rw [admissionCall, restatedDevelopment_data, restatedTheory_data]
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Negative**: twenty-six steps take the call of the admission of a term
whose sort is not declared to the reading of the refusal. -/
theorem admissionNames_refusal_replays :
    replayNamesCoded admissionTableNames admissionRefusalTraceNames
        (admissionCall [.term 0 ⟨[], 0, ∅⟩]) =
      some (datum constantSpelling (encodeTheoryResult none)) := by
  rw [admissionCall, undeclaredSort_data]
  decide +kernel

/-- **A reduction of exactly 225 steps**, in the theory of the table with the
family, from the call of the admission to the reading of the theory. -/
theorem admissionNames_instance_steps :
    StepsIn (withNames admissionTableNames) 225 (admissionCall restatedDevelopment)
      (datum constantSpelling (encodeTheoryResult (some restatedTheory))) := by
  have steps := replayNamesCoded_stepsIn admissionNames_stored admissionNames_instance_replays
  rwa [admissionTraceNames_parts.1] at steps

/-- **The candidate takes exactly 225 transitions** from the run of the
admission of the development to the run of its theory, in the space that
stores the table and the rules of the family for the names of the call. -/
theorem admissionNames_instance_run_steps :
    atomsReduceTheory.Steps 225 (admissionRunNames restatedDevelopment)
      (admittedRunNames restatedDevelopment (some restatedTheory)) :=
  localRun_steps admissionNames_stores.runnable (namesFor_covers _ _) (namesFor_within _ _)
    admissionNames_instance_steps

/-- **Negative**: the candidate takes exactly twenty-six transitions from the
run of the admission of a term whose sort is not declared to the run of the
refusal. -/
theorem admissionNames_refusal_run_steps :
    atomsReduceTheory.Steps 26 (admissionRunNames [.term 0 ⟨[], 0, ∅⟩])
      (admittedRunNames [.term 0 ⟨[], 0, ∅⟩] none) := by
  have steps := replayNamesCoded_stepsIn admissionNames_stored admissionNames_refusal_replays
  rw [admissionRefusalTraceNames_parts.1] at steps
  exact localRun_steps admissionNames_stores.runnable (namesFor_covers _ _) (namesFor_within _ _)
    steps

#print axioms admissionTraceNames_parts
#print axioms admissionNames_instance_replays
#print axioms admissionNames_refusal_replays
#print axioms admissionNames_instance_steps
#print axioms admissionNames_instance_run_steps
#print axioms admissionNames_refusal_run_steps

end Mettapedia.Logic.HostingStyles.NameEquality
