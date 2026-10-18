; Running closed rho processes on the GSLT program driver.
; Load after gslt_scoped_execution, gslt_typed_sites, gslt_execution_driver,
; gslt_rule_readout_cache, gslt_program_driver, gslt_program_resumption and
; gslt_rho_lex_canonical.
;
; The plan argument is the encoded depth-one rho plan,
;   (RhoPlan environment permissions bound expected rules):
; the COMM declaration with the root as its only reduction context. Every
; state is first put in lexicographic canonical form, where every rho step
; is a COMM at the root of the bag. One step runs the presentation entry
; with the given budget and takes the first released receipt. Released
; receipts only grow under more work, so that first receipt is final.
; A state is quiescent only when the publication is complete and empty.

; A RhoSearch retains the canonical process and its ProgramObservation.
; The extra budget advances those pending jobs; it does not begin a new search.
; Read its observation with gslt:program:publication before committing a COMM.
(: rho:run:resume-search (-> Atom Atom %Undefined%))
(= (rho:run:resume-search $search $extra)
   (case $search
     (((RhoSearch $process $observation)
       (let $resumed (gslt:program:resume $observation $extra)
         (RhoSearch $process $resumed))))))

(: rho:run:step (-> Atom Atom Atom %Undefined%))
(= (rho:run:step $plan $process $budget)
   (case $plan
     (((RhoPlan $environment $permissions $bound $expected $rules)
       (let* (($canonical (rho:lex:canonical $process))
              ($observation (gslt:program:execute $environment $permissions $bound $expected $canonical
                $rules $budget))
              ($published (gslt:program:publication $observation)))
         (case $published
           (((ProgramPublication LNil ProgramPublicationComplete) (RhoQuiescent $canonical))
            ((ProgramPublication
               (LCons (RuleJobReceipt $job $trace $captured $completed $history $local $target) $others) $status)
             (RhoStepped $canonical $target))
            ((ProgramPublication $released $status) (RhoUnsaturated $canonical $status)))))))))

; At most `fuel` steps. The trace lists the canonical states in order and ends
; with RhoQuiescent, RhoFuelSpent or (RhoUnsaturated status).
(: rho:run (-> Atom Atom Atom Atom %Undefined%))
(= (rho:run $plan $process $fuel $budget)
   (if (== $fuel 0)
     (let $state (rho:lex:canonical $process) (RhoTrace (LCons $state LNil) RhoFuelSpent))
     (let $result (rho:run:step $plan $process $budget)
       (case $result
         (((RhoQuiescent $state) (RhoTrace (LCons $state LNil) RhoQuiescent))
          ((RhoStepped $state $next)
           (let* (($remaining (- $fuel 1))
                  ($rest (rho:run $plan $next $remaining $budget)))
             (case $rest
               (((RhoTrace $states $end) (RhoTrace (LCons $state $states) $end))))))
          ((RhoUnsaturated $state $status) (RhoTrace (LCons $state LNil) (RhoUnsaturated $status))))))))

; A RhoProcess retains the committed receipt history and one phase:
;   (RhoLive search) while a COMM search is pending,
;   (RhoDone process) after a completed empty search,
;   RhoCancelled after this local execution drops its pending search.
; History is chronological. Each RhoCommit keeps the receipt that licensed
; the step, including its binding and query provenance.
; Matcher budget stays on rho:run:resume-process. rho:run:advance counts
; committed COMM steps and does not add matcher budget.
; rho:run, rho:run:step and rho:run:resume-search are unchanged.

(: rho:run:append-commit (-> Atom Atom %Undefined%))
(= (rho:run:append-commit $history $commit)
   (case $history
     ((LNil (LCons $commit LNil))
      ((LCons $head $tail)
       (let $rest (rho:run:append-commit $tail $commit)
         (LCons $head $rest))))))

(: rho:run:begin (-> Atom Atom %Undefined%))
(= (rho:run:begin $plan $process)
   (case $plan
     (((RhoPlan $environment $permissions $bound $expected $rules)
       (let* (($canonical (rho:lex:canonical $process))
              ($observation (gslt:program:execute $environment $permissions $bound $expected $canonical
                $rules 0)))
         (RhoProcess LNil (RhoLive (RhoSearch $canonical $observation))))))))

(: rho:run:resume-process (-> Atom Atom %Undefined%))
(= (rho:run:resume-process $execution $extra)
   (case $execution
     (((RhoProcess $history (RhoLive $search))
       (let $resumed (rho:run:resume-search $search $extra)
         (RhoProcess $history (RhoLive $resumed))))
      ((RhoProcess $history (RhoDone $process))
       (RhoProcess $history (RhoDone $process)))
      ((RhoProcess $history RhoCancelled)
       (RhoProcess $history RhoCancelled)))))

; This constructs the successor of an already admitted receipt. Callers that
; accept external candidates use commit-published, which checks membership.
(: rho:run:after-receipt (-> Atom Atom Atom Atom %Undefined%))
(= (rho:run:after-receipt $plan $history $process $receipt)
   (case $plan
     (((RhoPlan $environment $permissions $bound $expected $rules)
       (case $receipt
         (((RuleJobReceipt $job $trace $captured $completed $events $local $target)
           (let* (($after (rho:lex:canonical $target))
                  ($successor (gslt:program:execute $environment $permissions $bound $expected $after
                    $rules 0))
                  ($committed (rho:run:append-commit $history
                    (RhoCommit $process $receipt $after))))
             (RhoProcess $committed (RhoLive (RhoSearch $after $successor)))))))))))

(: rho:run:commit (-> Atom Atom %Undefined%))
(= (rho:run:commit $plan $execution)
   (case $plan
     (((RhoPlan $environment $permissions $bound $expected $rules)
       (case $execution
         (((RhoProcess $history (RhoLive (RhoSearch $process $observation)))
           (let $published (gslt:program:publication $observation)
             (case $published
               (((ProgramPublication LNil ProgramPublicationComplete)
                 (RhoProcess $history (RhoDone $process)))
                ((ProgramPublication (LCons $receipt $others) ProgramPublicationComplete)
                 (rho:run:after-receipt $plan $history $process $receipt))
                ((ProgramPublication $released $status)
                 (RhoProcess $history (RhoLive (RhoSearch $process $observation))))))))
          ((RhoProcess $history (RhoDone $process))
           (RhoProcess $history (RhoDone $process)))
          ((RhoProcess $history RhoCancelled)
           (RhoProcess $history RhoCancelled))))))))

(: rho:run:commit-candidate (-> Atom Atom Atom %Undefined%))
(= (rho:run:commit-candidate $plan $execution $candidate)
   (case $execution
     (((RhoProcess $history (RhoLive (RhoSearch $process $observation)))
       (let $published (gslt:program:publication $observation)
         (case $published
           (((ProgramPublication (LCons $receipt $others) ProgramPublicationComplete)
             (if (== $candidate $receipt)
               (rho:run:commit $plan $execution)
               $execution))
            ((ProgramPublication $released $status) $execution)))))
      ((RhoProcess $history (RhoDone $process)) $execution)
      ((RhoProcess $history RhoCancelled) $execution))))

(: rho:run:cancel (-> Atom %Undefined%))
(= (rho:run:cancel $execution)
   (case $execution
     (((RhoProcess $history (RhoLive $search))
       (RhoProcess $history RhoCancelled))
      ((RhoProcess $history (RhoDone $process))
       (RhoProcess $history RhoCancelled))
      ((RhoProcess $history RhoCancelled)
       (RhoProcess $history RhoCancelled)))))

(: rho:run:advance (-> Atom Atom Atom %Undefined%))
(= (rho:run:advance $plan $execution $fuel)
   (if (== $fuel 0)
     $execution
     (let* (($stepped (rho:run:commit $plan $execution))
            ($remaining (- $fuel 1)))
       (rho:run:advance $plan $stepped $remaining))))

; A completed publication permits any of its distinct receipt occurrences.
; Equal result values do not identify their matcher paths or source positions.
(: rho:run:contains-receipt (-> Atom Atom %Undefined%))
(= (rho:run:contains-receipt $candidate $receipts)
   (case $receipts
     ((LNil false)
      ((LCons $receipt $rest)
       (if (== $candidate $receipt)
         true
         (rho:run:contains-receipt $candidate $rest))))))

(: rho:run:commit-published (-> Atom Atom Atom %Undefined%))
(= (rho:run:commit-published $plan $execution $candidate)
   (case $execution
     (((RhoProcess $history (RhoLive (RhoSearch $process $observation)))
       (let $published (gslt:program:publication $observation)
         (case $published
           (((ProgramPublication $receipts ProgramPublicationComplete)
             (if (rho:run:contains-receipt $candidate $receipts)
               (rho:run:after-receipt $plan $history $process $candidate)
               $execution))
            ((ProgramPublication $released $status) $execution)))))
      ((RhoProcess $history (RhoDone $process)) $execution)
      ((RhoProcess $history RhoCancelled) $execution))))

; Occurrence cells use stable identifiers. RhoFresh and RhoSpent differ:
; a consumed identifier is never an available allocation identifier.
; Reads and writes both use (RhoCell key value). Store rows are newest first.
(: rho:run:cell-read (-> Atom Atom %Undefined%))
(= (rho:run:cell-read $cells $key)
   (case $cells
     ((LNil RhoFresh)
      ((LCons (RhoCell $found $value) $rest)
       (if (== $key $found) $value (rho:run:cell-read $rest $key))))))

(: rho:run:validate-reads (-> Atom Atom %Undefined%))
(= (rho:run:validate-reads $cells $reads)
   (case $reads
     ((LNil true)
      ((LCons (RhoCell $key $expected) $rest)
       (let $current (rho:run:cell-read $cells $key)
         (if (== $current $expected)
           (rho:run:validate-reads $cells $rest)
           false))))))

(: rho:run:apply-writes (-> Atom Atom %Undefined%))
(= (rho:run:apply-writes $cells $writes)
   (case $writes
     ((LNil $cells)
      ((LCons (RhoCell $key $value) $rest)
       (rho:run:apply-writes (LCons (RhoCell $key $value) $cells) $rest)))))

; Validation is separate from permission to propose a COMM. A proposal must
; also carry a checked COMM derivation before its writes count as a rho step.
(: rho:run:commit-cells (-> Atom Atom %Undefined%))
(= (rho:run:commit-cells $cells $proposal)
   (case $proposal
     (((RhoProposal $reads $writes)
       (if (rho:run:validate-reads $cells $reads)
         (let $next (rho:run:apply-writes $cells $writes) (RhoCellsAccepted $next))
         (RhoCellsRefused $cells))))))
