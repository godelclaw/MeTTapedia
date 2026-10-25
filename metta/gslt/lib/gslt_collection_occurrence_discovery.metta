; Discover retained matcher lanes from the current source's typed rule jobs.
(: gslt:occurrence-discovery:variant (-> Atom Atom %Undefined%))
(= (gslt:occurrence-discovery:variant $job $variant)
  (case $job
    (((RuleJob $ordinal
        (RuleJobDeclaration $position
          (ScopedRewriteRuleV1 $label $types $premises $left $right $binding)
          (RuleBindingPlan $spec $origin)) $original-site)
      (case $variant
        (((CollectionSiteVariant $old-site
            (RuleJobSite $address $context $focus $bound $type $frames))
          (let* (($elaborated-types (gslt:collection-search:elaborated-types $types $origin))
                 ($rule (ScopedRewriteRuleV1 $label $elaborated-types $premises $left $right
                          (RuleBindingSome $spec)))
                 ($ambient (gslt:automata:length $bound))
                 ($request (ScopedMatcherRequest $rule $spec $ambient RuleLeft LNil 0 LNil $left $focus))
                 ($occurrence (RecursiveOccurrenceJob $job $variant)))
            (gslt:occurrence-matcher:begin $occurrence $request)))))))))

(: gslt:occurrence-discovery:variants (-> Atom Atom %Undefined%))
(= (gslt:occurrence-discovery:variants $job $variants)
  (case $variants
    ((LNil LNil)
     ((LCons $variant $rest)
      (let* (($lane (gslt:occurrence-discovery:variant $job $variant))
             ($later (gslt:occurrence-discovery:variants $job $rest)))
        (LCons $lane $later))))))

(: gslt:occurrence-discovery:jobs (-> Atom %Undefined%))
(= (gslt:occurrence-discovery:jobs $jobs)
  (case $jobs
    ((LNil LNil)
     ((LCons $job $rest)
      (case $job
        (((RuleJob $ordinal $declaration $site)
          (let* (($variants (gslt:collection-context:site-variants $site))
                 ($here (gslt:occurrence-discovery:variants $job $variants))
                 ($later (gslt:occurrence-discovery:jobs $rest)))
            (gslt:automata:append $here $later)))))))))

(: gslt:occurrence-discovery:begin (-> Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:occurrence-discovery:begin $declarations $free $permissions $bound $expected $source $rules)
  (let* (($jobs (gslt:sites:jobs $declarations $free $permissions $bound $expected $source $rules))
         ($lanes (gslt:occurrence-discovery:jobs $jobs)))
    (gslt:occurrence-machine:from-lanes $lanes)))
