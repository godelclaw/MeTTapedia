;; ============================================================================
;; Iter Architecture MeTTa + Megalodon Verification Suite Runner
;;
;; Run from the MeTTapedia repository root:
;;   cetta --lang petta megalodon/iter/verify_iter.metta
;;
;; Verifies all four Megalodon formalization modules against the standard Egal
;; preamble (megalodon/ramsey36/preamble.mgs) via CeTTa's native Megalodon
;; kernel (library megalodon), and mechanically audits every verdict:
;;   verified, 0 document axioms, 0 admitted, 0 aby, 0 dependent,
;;   0 unfinished, 0 out-of-budget.
;; ============================================================================

!(import! &self (library megalodon))
!(import! &self (library system))

(= (iter-verify:preamble)
   ("megalodon/ramsey36/preamble.mgs"))

(= (iter-verify:fail $msg)
   (let $_ (println! (IterVerifyFailed $msg))
     (system:exit 1)))

(= (iter-verify:assert-true $label $cond)
   (if $cond
       (Ok $label)
       (iter-verify:fail (AssertionFailed $label))))

(= (iter-verify:check-mg $path $expected_count)
   (let $doc (mg:check-document (iter-verify:preamble) $path ())
     (case $doc
       (((Megalodon.document $theory $authority verified
            (summary (theorems $nt) (checked $nc) (verified $nv)
                     (admitted 0) (aby 0) (dependent 0)
                     (unfinished 0) (out-of-budget 0)
                     (document-axioms 0) (aby-steps-tried 0) (aby-steps-proved 0))
            $entries)
         (if (and (== $nt $nc) (and (== $nt $nv) (== $nt $expected_count)))
             (let $_ (println! (MegalodonVerified $path (theorems $nv) (document-axioms 0) (admitted 0) (aby 0)))
               $nv)
             (iter-verify:fail (CountMismatch $path $expected_count $nt $nc $nv))))
        ($other (iter-verify:fail (DocumentNotVerified $path $other)))))))

(= (iter-verify:main)
   (let* (($n1 (iter-verify:check-mg "megalodon/iter/01_nal_truth.mg" 63))
          ($n2 (iter-verify:check-mg "megalodon/iter/02_experience_hygiene.mg" 56))
          ($n3 (iter-verify:check-mg "megalodon/iter/03_loop_state_machine.mg" 46))
          ($n4 (iter-verify:check-mg "megalodon/iter/04_data_boundaries.mg" 48))
          ($total (+ (+ $n1 $n2) (+ $n3 $n4)))
          ($_ (iter-verify:assert-true "grand-total-213" (== $total 213))))
     (println! (IterVerificationSuitePass
                 (megalodon-modules 4)
                 (theorems $total)
                 (document-axioms 0)
                 (admitted 0)
                 (aby 0)))))

!(iter-verify:main)
