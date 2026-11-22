;; ============================================================================
;; Iter Architecture MeTTa + Megalodon Verification Suite Runner
;;
;; Run from the MeTTapedia repository root:
;;   cetta --lang petta megalodon/iter/verify_iter.metta
;;
;; 1. Verifies all four Megalodon formalization modules against the standard
;;    Egal preamble (megalodon/ramsey36/preamble.mgs) via CeTTa's native
;;    Megalodon kernel (library megalodon), mechanically auditing every verdict:
;;      verified, 0 document axioms, 0 admitted, 0 aby, 0 dependent,
;;      0 unfinished, 0 out-of-budget.
;; 2. Cross-checks the executable MeTTa cadence model (pre-strip vs post-strip
;;    vs startup delay) against the proved Megalodon theorems in Module 2.
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

(= (iter-verify:assert-eq $label $got $want)
   (if (== $got $want)
       (Ok $label)
       (iter-verify:fail (EqMismatch $label (got $got) (want $want)))))

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

;; ----------------------------------------------------------------------------
;; Executable MeTTa cross-check of the Module 2 multi-step cadence theorems
;; Mirrors cad_step / cad_run in megalodon/iter/02_experience_hygiene.mg
;; ----------------------------------------------------------------------------

(= (iter-cad:bucket20 $n)
   (floor-math (/ $n 20)))

(= (iter-cad:step $policy $k (Cad $n $b $c))
   (let* (($cb (iter-cad:bucket20 $n))
          ($fired (> $cb $b))
          ($b1 (if $fired $cb $b))
          ($c1 (if $fired (+ $c 1) $c))
          ($trimmed (>= $n 100))
          ($n2 (if $trimmed (- 80 $k) $n))
          ($b2 (if $trimmed
                   (if (== $policy pre-strip)
                       (iter-cad:bucket20 80)
                       (iter-cad:bucket20 (- 80 $k)))
                   $b1)))
     (Cad (+ $n2 1) $b2 $c1)))

(= (iter-cad:run $policy $k $st $t)
   (if (<= $t 0)
       $st
       (iter-cad:run $policy $k (iter-cad:step $policy $k $st) (- $t 1))))

(= (iter-verify:check-cadence-crosscheck)
   (let* (;; Original pre-strip: uniformly 1 cleanup per closed (20+k)-step cycle for ALL 0<=k<=80
          ($_ (iter-verify:assert-eq "pre-strip-k0"  (iter-cad:run pre-strip  0 (Cad 81 4 0)  20) (Cad 81 4 1)))
          ($_ (iter-verify:assert-eq "pre-strip-k1"  (iter-cad:run pre-strip  1 (Cad 80 4 0)  21) (Cad 80 4 1)))
          ($_ (iter-verify:assert-eq "pre-strip-k5"  (iter-cad:run pre-strip  5 (Cad 76 4 0)  25) (Cad 76 4 1)))
          ($_ (iter-verify:assert-eq "pre-strip-k20" (iter-cad:run pre-strip 20 (Cad 61 4 0)  40) (Cad 61 4 1)))
          ($_ (iter-verify:assert-eq "pre-strip-k45" (iter-cad:run pre-strip 45 (Cad 36 4 0)  65) (Cad 36 4 1)))
          ($_ (iter-verify:assert-eq "pre-strip-k80" (iter-cad:run pre-strip 80 (Cad  1 4 0) 100) (Cad  1 4 1)))
          ;; Post-strip: 1 cleanup/cycle for k=0, 2 cleanups/cycle for 1<=k<=20
          ($_ (iter-verify:assert-eq "post-strip-k0"  (iter-cad:run post-strip  0 (Cad 81 4 0) 20) (Cad 81 4 1)))
          ($_ (iter-verify:assert-eq "post-strip-k1"  (iter-cad:run post-strip  1 (Cad 80 3 0) 21) (Cad 80 3 2)))
          ($_ (iter-verify:assert-eq "post-strip-k5"  (iter-cad:run post-strip  5 (Cad 76 3 0) 25) (Cad 76 3 2)))
          ($_ (iter-verify:assert-eq "post-strip-k20" (iter-cad:run post-strip 20 (Cad 61 3 0) 40) (Cad 61 3 2)))
          ;; Startup delay: uncleaned loaded history at L0=80 with k=0 has 0 cleanups across [80..99]
          ($_ (iter-verify:assert-eq "startup-delay-pre"  (iter-cad:run pre-strip  0 (Cad 80 4 0) 20) (Cad 100 4 0)))
          ($_ (iter-verify:assert-eq "startup-delay-post" (iter-cad:run post-strip 0 (Cad 80 4 0) 20) (Cad 100 4 0))))
     (println! (MeTTaCadenceCrossCheckPass (checks 12)))))

(= (iter-verify:main)
   (let* (($n1 (iter-verify:check-mg "megalodon/iter/01_nal_truth.mg" 63))
          ($n2 (iter-verify:check-mg "megalodon/iter/02_experience_hygiene.mg" 114))
          ($n3 (iter-verify:check-mg "megalodon/iter/03_loop_state_machine.mg" 46))
          ($n4 (iter-verify:check-mg "megalodon/iter/04_data_boundaries.mg" 48))
          ($total (+ (+ $n1 $n2) (+ $n3 $n4)))
          ($_ (iter-verify:assert-true "grand-total-271" (== $total 271)))
          ($_ (iter-verify:check-cadence-crosscheck)))
     (println! (IterVerificationSuitePass
                 (megalodon-modules 4)
                 (theorems $total)
                 (cadence-crosschecks 12)
                 (document-axioms 0)
                 (admitted 0)
                 (aby 0)))))

!(iter-verify:main)
