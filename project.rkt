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
   [note (mini-num number?)
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
  `TODO)

;; ==========================================================
;;                           INTERP
;; ==========================================================

(define (interp expr)
  `TODO)
