; Resumption and publication of program runs.
; Load after gslt_scoped_execution, gslt_typed_sites, gslt_execution_driver,
; gslt_rule_readout_cache and gslt_program_driver.
;
; A ProgramObservation keeps every job's whole machine state. Resuming it adds
; work to each job and never restarts one; the second argument is extra work
; per job. The flat receipt list of a ProgramObservation is a snapshot of the
; jobs' current receipts, not a stream prefix: more work on an earlier job can
; insert receipts before those already listed for a later job.
;
; Publication is the prefix that can be released in job order: the receipts of
; the complete earlier jobs, then the current receipts of the first job that is
; not complete. Every later job is withheld. A drained job with unresolved
; obligations blocks publication of the jobs after it.
;
; The domain is observations produced by gslt:program:run or by this resume:
; requests are unchanged and inner answers only grow. This file is not an
; admission checker and does not validate a forged checkpoint.

(: gslt:program:resume-job (-> Atom Atom %Undefined%))
(= (gslt:program:resume-job $observation $extra)
   (case $observation
     (((ProgramJobObservation
         (RuleJobRequestProjection $environment $permissions $bound $expected $source $job)
         $state $receipts)
       (let $request
         (RuleJobRequestProjection $environment $permissions $bound $expected $source $job)
         (let (Some (PremiseState $agenda $answers $unresolved $work))
           (gslt:premise:machine-run $environment $extra $state)
           (let $readouts (gslt:rule:job-readouts $request $answers)
             (let $current (gslt:program:receipts $readouts)
               (ProgramJobObservation $request
                 (PremiseState $agenda $answers $unresolved $work) $current)))))))))

(: gslt:program:resume-jobs (-> Atom Atom %Undefined%))
(= (gslt:program:resume-jobs $observations $extra)
   (case $observations
     ((LNil (ProgramObservation LNil LNil))
      ((LCons $observation $rest)
       (let (ProgramJobObservation $request $state $receipts)
         (gslt:program:resume-job $observation $extra)
         (let (ProgramObservation $later $laterReceipts)
           (gslt:program:resume-jobs $rest $extra)
           (let $all (gslt:automata:append $receipts $laterReceipts)
             (ProgramObservation
               (LCons (ProgramJobObservation $request $state $receipts) $later)
               $all))))))))

(: gslt:program:resume (-> Atom Atom %Undefined%))
(= (gslt:program:resume $observation $extra)
   (case $observation
     (((ProgramObservation $observations $snapshot)
       (gslt:program:resume-jobs $observations $extra)))))

; Publication reads each job's own state and receipts, not the flat snapshot.
(: gslt:program:publication-from (-> Atom %Undefined%))
(= (gslt:program:publication-from $observations)
   (case $observations
     ((LNil (ProgramPublication LNil ProgramPublicationComplete))
      ((LCons (ProgramJobObservation $request (PremiseState LNil $answers LNil $work) $receipts) $rest)
       (let (ProgramPublication $later $status)
         (gslt:program:publication-from $rest)
         (let $all (gslt:automata:append $receipts $later)
           (ProgramPublication $all $status))))
      ((LCons (ProgramJobObservation $request (PremiseState LNil $answers $unresolved $work) $receipts)
         $rest)
       (ProgramPublication $receipts ProgramPublicationBlocked))
      ((LCons (ProgramJobObservation $request $state $receipts) $rest)
       (ProgramPublication $receipts ProgramPublicationPending)))))

(: gslt:program:publication (-> Atom %Undefined%))
(= (gslt:program:publication $observation)
   (case $observation
     (((ProgramObservation $observations $snapshot)
       (gslt:program:publication-from $observations)))))
