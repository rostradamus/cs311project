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

;; parse : l-exp -> L-Expr
;; Consumes an l-expression and generates the corresponding L-Expr
(define (parse lexp)
  (match lexp
    [(list (? number? a) expr)
     (`TODO)]
    [(list 'note (? number? midi) (? number? start) (? number? duration))
     (`TODO)]
    [(list 'loop comps (? number? start) (? number? duration) (? number? iteration))
     (loop (map parse comps) start duration iteration)]
    [(list 'segment comps (? number? total))
     (segment (map parse comps) total)]
    ))

;; ==========================================================
;;                           INTERP
;; ==========================================================
(define (interp expr)
  `TODO)
