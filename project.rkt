#lang plai

;; ==========================================================
;;                     EBNF & DEFINE-TYPES
;; ==========================================================


;; L-Expr = Loop expression
;;
;; <L-Expr> ::=
;;             | {note <num> <num> <num>}
;;             | {<num> <L-Expr>}
;;             | {loop <L-Expr>* <num> <num> <num>}
;;             | {segment <L-Expr>* <num>}

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
;;                           INTERP
;; ==========================================================
(define (interp lexpr)
  (type-case L-Expr lexpr
    [note (midi start duration) `TODOnote]
    [modify-speed (multiplier expr) `TODOmodifyspeed]
    [loop (listExpr start duration iteration) `TODOloop]
    [segment (listExpr total) `TODOsegment]
    ))

;; ==========================================================
;;                           TESTS
;; ==========================================================

(test (parse '{note 1 1 1}) (note 1 1 1))
(test (parse '{1 {note 1 1 1}}) (modify-speed 1 (note 1 1 1)))
(test (parse '{loop (list {note 1 1 1}) 1 1 1}) (loop {note 1 1 1} 1 1 1))