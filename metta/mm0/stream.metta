; Read one already encoded request at a time, retaining only checked state.
; The frontend emits calls to start, submit and finish, never arbitrary code.
(: mm0:stream (-> %Undefined%))
(= (mm0:stream)
   (let $request (readln!)
     (case $request
       ((end_of_file MM0:End)
        ($call (let $answer (eval $call)
                 (let $printed (println! $answer) (mm0:stream))))))))
!(mm0:stream)
