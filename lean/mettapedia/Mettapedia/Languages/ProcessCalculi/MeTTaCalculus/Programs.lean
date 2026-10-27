import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.Determinacy
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.SearchScheduling
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.Chain
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.TopLevel
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.Success
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.JustWorks
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.SequentialBubble

/-!
# Programs as processes

A program runs as a system of commits over the occurrence store of the interaction basis.

* `Determinacy`: when the outcome does not depend on the scheduler, as a property of the rights
  processes hold (Keller's theorem for commits; the exact facet-conflict criterion; CALM; Kahn).
* `SearchScheduling`: search and scheduling as two nondeterminisms, where they coincide, and how
  today's effectful alternatives mix them.
* `Chain`: a program's continuation as a chain of private tokens; every scheduler runs it in order.
* `TopLevel`: the file, the REPL, budgets and resumption, fairness, and the reflected agenda.
* `Success`: success as an observation (may and must tests), cheap awaits, fixed-point detection.
* `JustWorks`: correctness without confluence; a first-come server and a race.
* `SequentialBubble`: sequential code as a bubble with its verdict theorem.
-/
