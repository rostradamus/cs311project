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
         (duration number?)
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
    [note (midi-num start-bar dur)
          (define buffer
            (* (- dur start-bar)
               FRAME-RATE))
          (assemble
           (list
            (list (silence buffer) 0)
            (list
             (synth-note
              "main"
              10
              midi-num
              (* FRAME-RATE dur))
             buffer)))]
    [modify-speed (multiplier expr) (resample multiplier (interp lexpr))]
    [loop (exprs sbar dur iter)
          ;Assume processed returns a recursively processed rsound of all exprs,
          ;and that buffer handles similarly to the implementation in the note case
          #;(local
            [(define processed
                    exprs)
            (define buffer
               (* (- dur sbar)
                  FRAME-RATE))
             (define loopSound
               (assemble (list
                          (list (silence buffer) 0)
                          (list processed buffer)))
               )
            (define (rec-append s acc)
               (if0 acc
                    s
                    (rec-append
                     (rs-append s s)
                     (sub1 acc))))]
          (rec-append loopSound iter))
          `TODO]
    [segment (exprs total-length)
             ;Assume processed returns a recursively processed rsound of all exprs
             #;(local [(define processed
                       exprs)]
                     (clip processed
                           0
                           (* FRAME-RATE total-length)))
             'TODO]
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


(play (interp (segment
               ((note 60 0 0.5)
              (note 60 0 0.5)
              (note 67 0 0.5)
              (note 67 0 0.5)
              (note 69 0 0.5)
              (note 69 0 0.5)
              (note 67 0 0.5)) 5)))