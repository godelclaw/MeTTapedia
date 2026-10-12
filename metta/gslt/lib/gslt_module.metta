; Ordered assembly of complete LanguageDef fragments. Every row family is
; retained, including equations and duplicate rewrites. Assembly precedes
; whole-language validation and does not resolve shared-origin imports.
; Load gslt_match_automata.metta for the canonical list append operation.

(: gslt:module:assemble (-> Atom Atom %Undefined%))
(= (gslt:module:assemble $name $fragments)
   (case $fragments
     ((LNil (Some (GSLTLanguageDefWireV1 $name LNil LNil LNil LNil)))
      ((LCons (GSLTLanguageDefWireV1 $local $types $terms $equations $rewrites) $rest)
       (case (gslt:module:assemble $name $rest)
         (((Some (GSLTLanguageDefWireV1 $assembled $tail-types $tail-terms $tail-equations $tail-rewrites))
           (let* (($all-types (gslt:automata:append $types $tail-types))
                  ($all-terms (gslt:automata:append $terms $tail-terms))
                  ($all-equations (gslt:automata:append $equations $tail-equations))
                  ($all-rewrites (gslt:automata:append $rewrites $tail-rewrites)))
             (Some (GSLTLanguageDefWireV1 $name $all-types $all-terms $all-equations $all-rewrites))))
          ($bad None))))
      ($bad None))))

; Execute only after all fragments have been assembled. Recursive premises
; consult the assembled language, so their witnesses may cross fragments.
; Load gslt_rule_execution.metta for contextual execution.
(: gslt:module:reducts (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:module:reducts $name $fragments $strategy $rows $depth $subject)
   (case (gslt:module:assemble $name $fragments)
     (((Some $assembled)
       (gslt:rule:language-contextual-reducts $strategy $assembled $rows $depth $subject))
      ($bad None))))

; Checked imports use full declaration identities. CoherentOriginV1 requires
; agreement at a shared origin; StructuralOriginViewV1 permits different
; exposed views of that origin. Both refuse unequal declarations at one label.
; These operations deduplicate declarations, never the rule rows in a body.
(: gslt:module:compatible (-> Atom Atom Atom %Undefined%))
(= (gslt:module:compatible $mode $left $right)
   (case ($left $right)
     ((((ModuleEntry $origin $label $body) (ModuleEntry $other-origin $other-label $other-body))
       (case $mode
         ((CoherentOriginV1
           (if (== $left $right) True
             (if (== $origin $other-origin) False
               (if (== $label $other-label) False True))))
          (StructuralOriginViewV1
           (if (== $label $other-label) (== $left $right) True))
          ($bad False))))
      ($bad False))))

(: gslt:module:insert (-> Atom Atom Atom %Undefined%))
(= (gslt:module:insert $mode $entry $kept)
   (case $entry
     (((ModuleEntry $origin $label $body)
       (case $kept
         ((LNil (Some (LCons $entry LNil)))
          ((LCons $first $rest)
           (if (== $entry $first) (Some $kept)
             (if (gslt:module:compatible $mode $first $entry)
               (case (gslt:module:insert $mode $entry $rest)
                 (((Some $tail) (Some (LCons $first $tail)))
                  ($bad None)))
               None)))
          ($bad None))))
      ($bad None))))

(: gslt:module:fold (-> Atom Atom Atom %Undefined%))
(= (gslt:module:fold $mode $kept $incoming)
   (case $incoming
     ((LNil (Some $kept))
      ((LCons $entry $rest)
       (case (gslt:module:insert $mode $entry $kept)
         (((Some $next) (gslt:module:fold $mode $next $rest))
          ($bad None))))
      ($bad None))))

(: gslt:module:check (-> Atom Atom %Undefined%))
(= (gslt:module:check $mode $entries)
   (case $mode
     ((CoherentOriginV1 (gslt:module:fold $mode LNil $entries))
      (StructuralOriginViewV1 (gslt:module:fold $mode LNil $entries))
      ($bad None))))

(: gslt:module:join (-> Atom Atom Atom %Undefined%))
(= (gslt:module:join $mode $left $right)
   (case (gslt:module:check $mode $left)
     (((Some $kept) (gslt:module:fold $mode $kept $right))
      ($bad None))))

(: gslt:module:bodies (-> Atom %Undefined%))
(= (gslt:module:bodies $entries)
   (case $entries
     ((LNil LNil)
      ((LCons (ModuleEntry $origin $label $body) $rest)
       (let $tail (gslt:module:bodies $rest) (LCons $body $tail))))))

(: gslt:module:import-reducts (-> Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:module:import-reducts $mode $name $left $right $strategy $rows $depth $subject)
   (case (gslt:module:join $mode $left $right)
     (((Some $entries)
       (let $fragments (gslt:module:bodies $entries)
         (gslt:module:reducts $name $fragments $strategy $rows $depth $subject)))
      ($bad None))))
