#lang plai
(require rsound)

;; ==========================================================
;;                     EBNF & DEFINE-TYPES
;; ==========================================================


;; L-Expr = Loop expression
;;
;; <L-Expr> ::=
;;             | {note <num> <num> <num>}
;;             | {<num> <L-Expr>}
;;             | {loop <L-Expr>+ <num> <num> <num>}
;;             | {segment <L-Expr>+ <num>}

(define-type L-Expr
  [id (name symbol?)]
  [note (midi-num number?)
        (start-bar number?)
        (duration number?)]
  [modify-speed (multiplier number?)
                (expr L-Expr?)]
  [loop (comps (listof L-Expr?))
        (start-bar number?)
        (end-bar number?)
        (iteration number?)]
  [segment (comps (listof L-Expr?))
           (total-bars number?)]
  [with (names (listof symbol?))
        (named-exprs (listof L-Expr?))
        (body L-Expr?)]
  )

;; ==========================================================
;;                           PARSE
;; ==========================================================

;; reserved? : symbol -> boolean
(define (reserved? word)
  (if (member word '(note loop segment with id))
      #t
      #f))

;; parse : l-exp -> L-Expr
;; Consumes an l-expression and generates the corresponding L-Expr
(define (parse lexp)
  (local [(define (valid-id? sym)
            (and (symbol? sym)
                 (not (reserved? sym))))]
    (match lexp
      [(? valid-id?) (id lexp)]
      [(list 'note (? number? midi) (? number? start) (? number? duration))
       (note midi start duration)]
      [(list (? number? multiplier) expr)
       (modify-speed multiplier (parse expr))]
      [(list 'loop comps (? number? start) (? number? duration) (? number? iteration))
       (loop (map parse comps) start duration iteration)]
      [(list 'segment comps (? number? total))
       (segment (map parse comps) total)]
      [(list 'with (list (list (and (? valid-id?) ids) binding-exprs) ...) body-expr)
       (with ids (map parse binding-exprs) (parse body-expr))]
      [(cons (and word (? reserved?)) _)
       (error 'parse "Misused reserved word ~a in: ~a" word lexp)]
      [_
       (error 'parse "Unable to recognize expr: ~a" lexp)]
      )))

;; ==========================================================
;;                           PARSE TESTS
;; ==========================================================
;; simple tests with notes as L-Expr

(test (parse 'x) (id 'x))
(test (parse 'note-40) (id 'note-40))
(test/exn (parse 'id) "")
(test/exn (parse 'loop) "")
(test/exn (parse 'with) "")

(test (parse '{note 1 1 1}) (note 1 1 1))
(test (parse '{1 {note 1 1 1}}) (modify-speed 1 (note 1 1 1)))

(test (parse '{loop ((note 1 1 1)) 1 1 1})
      (loop (list (note 1 1 1)) 1 1 1))
(test (parse '{loop ((note 1 1 1) (note 2 2 2) (note 3 3 3)) 4 4 4})
      (loop (list (note 1 1 1) (note 2 2 2) (note 3 3 3)) 4 4 4))

(test (parse '{segment ((note 1 1 1)) 2})
      (segment (list (note 1 1 1)) 2))
(test (parse '{segment ((note 1 1 1) (note 2 2 2)) 3})
      (segment (list (note 1 1 1) (note 2 2 2)) 3))

(test (parse '{with {{note-40 {note 40 1 4}}}
                    note-40})
      (with '(note-40) (list (note 40 1 4)) (id 'note-40)))
(test (parse '{with {{note-40 {note 40 1 4}}
                     {seg-1 {segment ((note 1 1 1) (note 2 2 2)) 3}}
                     {seg-2 {segment ((note 1 1 1)) 2}}
                     {loop-1 {loop ((note 1 1 1)) 1 1 1}}}
                    {loop {note-40 seg-1 seg-2 loop-1} 1 5 2}})
      (with '(note-40 seg-1 seg-2 loop-1)
            (list (note 40 1 4)
                  (segment (list (note 1 1 1) (note 2 2 2)) 3)
                  (segment (list (note 1 1 1)) 2)
                  (loop (list (note 1 1 1)) 1 1 1))
            (loop (list (id 'note-40)
                        (id 'seg-1)
                        (id 'seg-2)
                        (id 'loop-1))
                  1 5 2)))

;; ==========================================================
;;                           INTERP
;; ==========================================================

;; The environment that stores "deferred subs"
(define-type Env
  [mtEnv]
  [anEnv (name symbol?)
         (val rsound?)
         (restEnv Env?)])

;; lookup : symbol Env -> rsound
;; Find the value of name in env. Emit error if not found
(define (lookup name env)
  (local [(define (lookup-helper name env)
            (type-case Env env
              [mtEnv () (error 'lookup "free identifier: ~a" name)]
              [anEnv (bound-name bound-val rest-env)
                     (if (symbol=? bound-name name)
                         bound-val
                         (lookup-helper name rest-env))]))]
    (lookup-helper name env)))

(define (interp lexpr)
  (local [(define (interp expr)
            (error 'interp "SHOULDN'T REACH HERE"))
          (define (helper lexpr env)
            (type-case L-Expr lexpr
              ;[note (midi start duration) (synth-note "main" 10 midi (* FRAME-RATE duration))]
              [id (name) (lookup name env)]
              [note (midi-num start-bar end-bar)
                    (define validNote
                      (if (negative? (- end-bar start-bar))
                          false
                          true))
                    (define buffer
                      (* (- start-bar 1)
                         FRAME-RATE))
                    (if validNote
                        true
                        (error 'Note "failed because note end-bar is before start-bar"))
                    (if (zero? buffer) ;if buffer is 0 (no silence) just play the given note
                        (synth-note
                         "main"
                         10
                         midi-num
                         (round (* (- end-bar start-bar) FRAME-RATE)))
                        ;else add silence beforehand then play note
                        (rs-append
                         (silence (round buffer))
                         (synth-note
                          "main"
                          10
                          midi-num
                          (round (* (- end-bar start-bar) FRAME-RATE)))))]
              [modify-speed (multiplier expr) (resample multiplier (helper lexpr env))]
              [loop (exprs start-bar end-bar iter)
                    ;Assume processed returns a recursively processed rsound of all exprs,
                    ;and that buffer handles similarly to the implementation in the note case
                    (local [
                            (define processed
                              (assemble (map (lambda (n) (list n 0)) (map (lambda (e) (helper e env)) exprs))))
                            (define loopAcc processed)
                            (define (rec-append processed iter)
                              (for ([i (sub1 iter)])
                                (set! loopAcc (rs-append loopAcc processed)))
                              loopAcc)]
                      (rec-append processed iter))]
              [segment (exprs total-length)
                       ;Assume processed returns a recursively processed rsound of all exprs
                       (local [(define processed
                                 (assemble (map (lambda (n) (list n 0)) (map (lambda (e) (helper e env)) exprs))))]
                         (clip processed 1 (/ (* FRAME-RATE total-length) 2)))]
              [with (names named-exprs body)
                    (local [(define ne-vals
                              (map (lambda (expr) (helper expr env)) named-exprs))]
                      (helper body (foldl anEnv
                                          env
                                          names
                                          ne-vals)))]
              ))]
    (helper lexpr (mtEnv))))

;; ==========================================================
;;                           INTERP TESTS
;; ==========================================================

;; Segment cuts off music despite having more notes in list due to user specifying segment length
#;
(play (interp (parse '{segment (
                                {note 60 1 1.25}
                                {note 60 1.25 1.50}
                                {note 67 1.50 	1.75}
                                {note 67 1.75    2}
                                {note 69 2         2.25}
                                {note 69 2.25	2.5}
                                {note 67 2.50      3}
                                {note 65 3		3.25}
                                {note 65 3.25	3.50}
                                {note 64 3.50	3.75}
                                {note 64 3.75	4} ;;CUTS OFF HERE
                                {note 62 4		4.25}
                                {note 62 4.25	4.50}
                                {note 60 4.50	5}) 4})))

;; Raises an error because note starts on bar 2 and ends on bar 1
#;
(play (interp (parse '{note 60 2 1})))

;; TWINKLE TWINKLE LITTLE STAR

#;
(play (rs-append* (list
                   (synth-note "main" 10 60 (* FRAME-RATE 0.5))
                   (synth-note "main" 10 60 (* FRAME-RATE 0.5))
                   (synth-note "main" 10 67 (* FRAME-RATE 0.5))
                   (synth-note "main" 10 67 (* FRAME-RATE 0.5))
                   (synth-note "main" 10 69 (* FRAME-RATE 0.5))
                   (synth-note "main" 10 69 (* FRAME-RATE 0.5))
                   (synth-note "main" 10 67 (* FRAME-RATE 0.5))
                   )))
#;
(play (interp (parse
               '{loop ({segment (
                                 {note 60 1	 	1.25}
                                 {note 60 1.25 	1.50}
                                 {note 67 1.50 	1.75}
                                 {note 67 1.75 	2}
                                 {note 69 2         2.25}
                                 {note 69 2.25	2.5}
                                 {note 67 2.50      3}
                                 {note 65 3		3.25}
                                 {note 65 3.25	3.50}
                                 {note 64 3.50	3.75}
                                 {note 64 3.75	4}
                                 {note 62 4		4.25}
                                 {note 62 4.25	4.50}
                                 {note 60 4.50	5}) 5}

                       {segment (
                                 {note 67 5         5.25}
                                 {note 67 5.25	5.50}
                                 {note 65 5.50	5.75}
                                 {note 65 5.75	6}
                                 {note 64 6 	6.25}
                                 {note 64 6.25	6.50}
                                 {note 62 6.50	7}) 5}

                       {segment (
                                 {note 67 7         7.25}
                                 {note 67 7.25	7.50}
                                 {note 65 7.50	7.75}
                                 {note 65 7.75	8}
                                 {note 64 8 	8.25}
                                 {note 64 8.25	8.50}
                                 {note 62 8.50	9}) 5}

                       {segment (
                                 {note 60 9	 	9.25}
                                 {note 60 9.25 	9.50}
                                 {note 67 9.50 	9.75}
                                 {note 67 9.75 	10}
                                 {note 69 10         10.25}
                                 {note 69 10.25	10.5}
                                 {note 67 10.50     11}
                                 {note 65 11	11.25}
                                 {note 65 11.25	11.50}
                                 {note 64 11.50	11.75}
                                 {note 64 11.75	12}
                                 {note 62 12	12.25}
                                 {note 62 12.25	12.50}
                                 {note 60 12.50	13}) 13}


                       ;Beatz
                       {loop (
                              {note 55 1 1.33}
                              {note 57 1.33 1.66}
                              {note 59 1.66 2}) 1 2 12}

                       )
                      1 7 2})))

;; Fly me to the moon - A test of very short notes
#;
(play (interp (parse
               '{loop ({segment (
                                 ;Treble Clef
                                 {note 70 1      1.10}
                                 {note 72 1.10   1.25}
                                 {note 71 1.25   1.50}
                                 {note 69 1.50   1.75}
                                 {note 67 1.75   1.85}
                                 {note 65 1.85   2.35}
                                 {note 67 2.35   2.50}
                                 {note 69 2.50   2.75}
                                 {note 72 2.75   3.0}
                                 {note 69 3.0    3.05}
                                 {note 70 3.05   3.10}
                                 {note 71 3.10   3.25}
                                 {note 69 3.25   3.50}
                                 {note 67 3.50   3.75}
                                 {note 65 3.75   3.85}
                                 {note 64 3.85   5}

                                 ;Bass Clef
                                 {note 55 1   1.25}
                                 {note 45 1   1.25}
                                 {note 55 1.25 1.5}
                                 {note 45 1.25 1.5}
                                 {note 55 1.5 1.75}
                                 {note 45 1.5 1.75}
                                 {note 55 1.75 2}
                                 {note 45 1.75 2}

                                 {note 60 2 2.25}
                                 {note 50 2 2.25}
                                 {note 60 2.25  2.5}
                                 {note 50 2.25  2.5}
                                 {note 60 2.5  2.75}
                                 {note 50 2.5  2.75}
                                 {note 60 2.75  3}
                                 {note 50 2.75  3}

                                 {note 43 3 3.33}
                                 {note 53 3 3.33}
                                 {note 43 3.33 3.66}
                                 {note 53 3.33 3.66}
                                 {note 43 3.66 4}
                                 {note 53 3.66 4}

                                 {note 59 4 4.33}
                                 {note 48 4 4.33}
                                 {note 59 4.33 4.66}
                                 {note 48 4.33 4.66}
                                 {note 59 4.66 5}
                                 {note 48 4.66 5}) 5}) 1 5 2})))

(play (interp (parse
               '{with {{treble-clef {segment {{note 70 1      1.10}
                                              {note 72 1.10   1.25}
                                              {note 71 1.25   1.50}
                                              {note 69 1.50   1.75}
                                              {note 67 1.75   1.85}
                                              {note 65 1.85   2.35}
                                              {note 67 2.35   2.50}
                                              {note 69 2.50   2.75}
                                              {note 72 2.75   3.0}
                                              {note 69 3.0    3.05}
                                              {note 70 3.05   3.10}
                                              {note 71 3.10   3.25}
                                              {note 69 3.25   3.50}
                                              {note 67 3.50   3.75}
                                              {note 65 3.75   3.85}
                                              {note 64 3.85   5}} 5}}
                       {base-clef {segment {{note 55 1   1.25}
                                            {note 45 1   1.25}
                                            {note 55 1.25 1.5}
                                            {note 45 1.25 1.5}
                                            {note 55 1.5 1.75}
                                            {note 45 1.5 1.75}
                                            {note 55 1.75 2}
                                            {note 45 1.75 2}

                                            {note 60 2 2.25}
                                            {note 50 2 2.25}
                                            {note 60 2.25  2.5}
                                            {note 50 2.25  2.5}
                                            {note 60 2.5  2.75}
                                            {note 50 2.5  2.75}
                                            {note 60 2.75  3}
                                            {note 50 2.75  3}

                                            {note 43 3 3.33}
                                            {note 53 3 3.33}
                                            {note 43 3.33 3.66}
                                            {note 53 3.33 3.66}
                                            {note 43 3.66 4}
                                            {note 53 3.66 4}

                                            {note 59 4 4.33}
                                            {note 48 4 4.33}
                                            {note 59 4.33 4.66}
                                            {note 48 4.33 4.66}
                                            {note 59 4.66 5}
                                            {note 48 4.66 5}} 5}}}
                      {loop (treble-clef base-clef) 1 5 2}})))
