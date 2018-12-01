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
  )

;; ==========================================================
;;                           PARSE
;; ==========================================================

;; reserved? : symbol -> boolean
(define (reserved? word)
  (if (member word '(note loop segment))
      #t
      #f))

;; parse : l-exp -> L-Expr
;; Consumes an l-expression and generates the corresponding L-Expr
(define (parse lexp)
  (match lexp
    [(list 'note (? number? midi) (? number? start) (? number? duration))
     (note midi start duration)]
    [(list (? number? multiplier) expr)
     (modify-speed multiplier (parse expr))]
    [(list 'loop comps (? number? start) (? number? duration) (? number? iteration))
     (loop (map parse comps) start duration iteration)]
    [(list 'segment comps (? number? total))
     (segment (map parse comps) total)]
    [(cons (and word (? reserved?)) _)
     (error 'parse "Misused reserved word ~a in: ~a" word lexp)]
    [_
     (error 'parse "Unable to recognize expr: ~a" lexp)]
    ))

;; ==========================================================
;;                           PARSE TESTS
;; ==========================================================
;; simple tests with notes as L-Expr

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

;; ==========================================================
;;                           INTERP
;; ==========================================================
(define (interp lexpr)
  (type-case L-Expr lexpr
    ;[note (midi start duration) (synth-note "main" 10 midi (* FRAME-RATE duration))]
    [note (midi-num start-bar end-bar)
          (define buffer
            (* (- start-bar 1)
               FRAME-RATE))
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
    [modify-speed (multiplier expr) (resample multiplier (interp lexpr))]
    [loop (exprs start-bar end-bar iter)
          ;Assume processed returns a recursively processed rsound of all exprs,
          ;and that buffer handles similarly to the implementation in the note case
          (local [
                  (define processed
                    (assemble (map (lambda (n) (list n 0)) (map interp exprs))))
                  (define loopAcc processed)
                  (define (rec-append processed iter)
                    (for ([i (sub1 iter)])
                      (set! loopAcc (rs-append loopAcc processed)))
                    loopAcc)]
            (rec-append processed iter))]
    [segment (exprs total-length)
             ;Assume processed returns a recursively processed rsound of all exprs
             (local [(define processed
                       (assemble (map (lambda (n) (list n 0)) (map interp exprs))))]
               processed)]
    ))

;; ==========================================================
;;                           INTERP TESTS
;; ==========================================================

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
                     
                     
       

