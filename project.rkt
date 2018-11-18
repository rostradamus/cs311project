#lang plai

;; ==========================================================
;;                     EBNF & DEFINE-TYPES
;; ==========================================================


;; L-Expr = Loop expression
;;
;; <L-Expr> ::=
;;             | {<num> <L-Expr>}
;;             | {note <num> <num> <num>}
;;             | {loop <L-Expr>* <num> <num> <num>}
;;             | {segment <L-Expr>* <num>}

(define-type L-Expr
   [modify-speed (multiplier number?)
                 (expr L-Expr?)]
   [note (midi-num number?)
         (start-bar number?)
         (duration number?)]
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
    [(list (? number? a) expr)
     (modify-speed a expr)]
    [(list 'note (? number? midi) (? number? start) (? number? duration))
     (note midi start duration)]
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
(define (interp expr)
  `TODO)
