#lang plai

;; TODO: Search for "TODO #" and fix the indicated problems.
;; We recommend fixing them in the order listed!

(require math/number-theory) ; for state threading tests

;; CS311 2018W1 Sequential Monte Carlo inference assignment
;; By Steven Wolfman and Sam Chow
;; Based on work by van de Meent et al, with particular thanks to Frank Wood.
;; See https://arxiv.org/pdf/1809.10756.pdf.
;; Any problems in this interpreter are purely our fault, however!
;;
;; This version of the interpreter based on work by:
;; Felipe Banados-Schwerter, Nico Ritschel, Syed Iqbal, Ziyang Jin,
;; Alex Gondek, Joanne Chen, Joey Eremondi, and Yiyun Xie.

(print-only-errors)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DO NOT TOUCH THIS CODE
;; Doing so will make *all our tests fail*
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (get-default-sampler)
  (let ([rng (vector->pseudo-random-generator
              (vector 1062772744 4224666480 3040273072
                      1729335656 1332042050 2620454108))])
    (lambda (outcomes)
      (list-ref outcomes (random (length outcomes) rng)))
    ))

(let*
    ([s (get-default-sampler)]
     [l '(1 2 3 4 5 6)]
     [result (list (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l)
                   (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l))])
  (if
   (equal? result '(6 1 1 3 3 5 6 2 2 4 4 4 3 2 4 6))
   "Random generator performing properly. Please do not mess with the generator code, or our tests will fail."
   (error 'get-default-sampler "Your random generator failed the sanity test with result ~v. Please notify the instructors immediately!" result)))



;; ==========================================================
;;                     EBNF & DEFINE-TYPES
;; ==========================================================


;; SMC = Sequential Monte Carlo Expression
;;
;; <Program> ::= {infer <number> <SMC>}  ; number must be a positive integer
;;
;; <SMC> ::= <number>
;;         | <string>
;;         | {distribution <SMC>}
;;         | {uniform <SMC> <SMC>}
;;         | {sample <SMC>}
;;         | {begin <SMC>+}
;;         | {observe <SMC> = <SMC>}
;;         | {<Binop> <SMC> <SMC>}
;;         | {ifelse <SMC> <SMC> <SMC>}
;;         | {with* {{<id> <SMC>}*} <SMC>}
;;         | {rec-with {<id> {<id>*} <SMC>} <SMC>}
;;         | {cons <SMC> <SMC>}
;;         | empty
;;         | {first <SMC>}
;;         | {rest <SMC>}
;;         | {empty? <SMC>}
;;         | {list <SMC>*}
;;         | {fun {<id>*} <SMC>}  ; no two ids may match
;;         | {<SMC> <SMC>*}
;;         | <id>
;;
;; <Binop> ::= + | - | * | < | > | = | <= | >= | %
;;
;; FURTHERMORE, the following functions are built-in:
;; + {range {lo hi} {ifelse {<= hi lo} empty {cons lo {range {+ lo 1} hi}}}}
;; + {nth {lst pos} {ifelse {<= pos 0} {first lst} {nth {rest lst} {- pos 1}}}}
;;
;; NOTES:
;; + {distribution E} evaluates E TO A NON-EMPTY LIST and turns it into a distV.
;; + {observe DE = VE} evaluates DE to a distV and VE to a value v and "observes"
;;     that the distribution's value is equal to the second value. It returns the
;;     resulting "distribution", but note that the distribution must be simply
;;     (distV (list v)).
;;
;;   observe does several other things, however. First, it updates the state (a
;;     likelihood) by multiplying it by the fraction of distribution values equal
;;     to v. If that likelihood multiplier is zero, then it rejects (but not
;;     before the next piece..). Second, it hands off the current computation
;;     just before the observe returns to the "controller", which can do what it
;;     wants with the computation. (It gives the controller: the current value +
;;     state just after the observe, the continuation representing the current
;;     computation, and the "name stack", which is just the value of the internal
;;     variable _STACK, and is used in SMC to represent the function call stack.)
;; + {ifelse C T E} evaluates C. Non-numeric values are errors. 0 is considered
;;     false (and so ifelse vealuates E in tail position). Anything else is true
;;     (and so ifelse evaluates T in tail position).
;; + defquery is gone, and infer is now "meta-linguistic" in a sense; that is,
;;     infer cannot be PART of a program but can only appear at the top level.
;;
;;   In PL terms, we've abandoned "orthogonality" for infer: it cannot be used
;;     wherever ordinary expressions are used. The SMC interpreter runs an infer
;;     by running the given number of computations, each starting at the query
;;     expression.
;; + {rec-with {FNAME {PNAME*} FBODY} BODY} defines a (possibly-recursive)
;;     function named FNAME with parameters PNAME* and body FBODY and then
;;     evaluates BODY in tail position (in an environment that includes FNAME).
;; + The with* form is the usual multi-armed with in which earlier bindings may
;;     be used in later named expressions (desugared internally to nested with,
;;     though with itself is now implemented directly)
;; + In fun, rec-with, and app, we allow multiple (and zero) parameter functions.
;; + We use Racket closures to implement our closures to make CPS conversion
;;     easier. This means that arity checking in function application happens
;;     only after we have evaluated the function expression AND all argument
;;     expressions.
;; + {uniform A B} is a discrete uniform distribution from A (inclusive) to B
;;     (excclusive). If A >= B, the distribution is empty (which is an error!).
;; + We've added standard list constructs.
;; + We've added string constant but ONLY the constants. NO operations aware
;;     of strings are available (e.g., taking lengths, appending, finding characters).
;;
;; Note: <id> cannot be a word used to introduce a special form (like with* or empty?)
;;       the word infer, or one of the binary operators. IN ADDITION, all identifiers
;;       beginning with an underscore _ (including just _ itself) are reserved.


;; Surface abstract syntax
(define-type S-SMC
  [s-num (n number?)]
  [s-distribution (list-exp S-SMC?)]
  [s-uniform (low S-SMC?) (high S-SMC?)]
  [s-sample (dist-exp S-SMC?)]
  [s-begin (exprs (listof S-SMC?))]
  [s-observe (dist S-SMC?) (ref-val S-SMC?)]
  [s-binop (op procedure?) (lhs S-SMC?) (rhs S-SMC?)]
  [s-with* (names (listof symbol?)) (named-exprs (listof S-SMC?)) (body S-SMC?)]
  [s-rec-with (fname symbol?) (params (listof symbol?)) (fbody S-SMC?) (body S-SMC?)]
  [s-ifelse (cond S-SMC?) (t S-SMC?) (e S-SMC?)]
  [s-cons (fst S-SMC?) (rst S-SMC?)]
  [s-empty]
  [s-first (exp S-SMC?)]
  [s-rest (exp S-SMC?)]
  [s-is-empty (exp S-SMC?)]
  [s-list (exps (listof S-SMC?))]
  [s-fun (params (listof symbol?)) (body S-SMC?)]
  [s-app (function S-SMC?) (args (listof S-SMC?))]
  [s-id (name symbol?)]
  [s-str (s string?)])

; Surface Program
(define-type S-Program
  [s-program (particles exact-positive-integer?) (query S-SMC?)])

; Desugared Abstract Syntax.
; Summaries of the desugarings are in comments inline.
(define-type D-SMC
  [d-num (n number?)]
  [d-distribution (list-exp D-SMC?)]
  ; {uniform e1 e2} => {distribution {_range e1 e2}}
  [d-sample (dist-exp D-SMC?)]
  ; {s-begin e1 e2 e3... en} => {with* {{_ e1} {_ e2} {_ e3}} en}
  [d-observe (dist D-SMC?) (ref-val D-SMC?)]
  [d-binop (op procedure?) (lhs D-SMC?) (rhs D-SMC?)]
  ; {with* {} e} => e; {with* {{n1 e1} {n2 e2}...} e} => {with {n1 e1} {with* {{n2 e2}...} e}}
  [d-with (name symbol?) (named-expr D-SMC?) (body D-SMC?)]
  [d-rec-with (fname symbol?) (params (listof symbol?)) (fbody D-SMC?) (body D-SMC?)]
  [d-ifelse (cond D-SMC?) (t D-SMC?) (e D-SMC?)]
  [d-cons (fst D-SMC?) (rst D-SMC?)]
  [d-empty]
  [d-first (exp D-SMC?)]
  [d-rest (exp D-SMC?)]
  [d-is-empty (exp D-SMC?)]
  ; {list} => empty; {list e1 e2...} => {cons e1 {list e2...}}
  [d-fun (params (listof symbol?)) (body D-SMC?)]
  [d-app (function D-SMC?) (args (listof D-SMC?))]
  [d-id (name symbol?)]
  [d-str (s string?)])

; Desugared program.
(define-type D-Program
  [d-program (particles exact-positive-integer?) (query D-SMC?)])



;; Environment mapping identifiers to values.
(define-type Env
  [mtEnv]
  [anEnv (name symbol?) (value SMC-Value?) (env Env?)])

;; Interpreting an Expression returns a SMC-Value
(define-type SMC-Value
  [numV (n number?)]
  [stringV (s string?)]
  [distV (values (and/c (listof SMC-Value?) (not/c empty?)))]
  [consV (first SMC-Value?) (rest SMC-Value?)]
  [emptyV]
  [rejectedV]
  [closureV (proc procedure?)])

;; SMC-Value->racket : SMC-Value -> ...
;; Tries to convert an SMC-Value to a corresponding racket value.
;; Gives up on rejected, dist, and closure.
(define (SMC-Value->racket value)
  (type-case SMC-Value value
    [numV (n) n]
    [stringV (s) s]
    [consV (f r) (cons (SMC-Value->racket f) (SMC-Value->racket r))]
    [emptyV () empty]
    [else (error 'SMC-Value->racket "Unable to convert ~a into a Racket value." value)]))

(test (SMC-Value->racket (numV 3)) 3)
(test (SMC-Value->racket (stringV "hello")) "hello")
(test (SMC-Value->racket (emptyV)) empty)
(test (SMC-Value->racket (consV (numV 2) (emptyV))) (list 2))

;; lookup : symbol Env -> SMC-Value
;; lookup looks up a variable name in a env
(define (lookup id env)
  (type-case Env env
    [mtEnv () (error 'lookup "unbound identifier ~a" id)]
    [anEnv (name value anotherEnv) (if (symbol=? id name)
                                       value
                                       (lookup id anotherEnv))]))

(test/exn (lookup 'x (mtEnv)) "")
(test/exn (lookup 'y (anEnv 'x (numV 1) (mtEnv))) "")
(test (lookup 'y (anEnv 'x (numV 1) (anEnv 'y (numV 2) (anEnv 'x (numV 3) (mtEnv))))) (numV 2))
(test (lookup 'x (anEnv 'x (numV 1) (anEnv 'y (numV 2) (anEnv 'x (numV 3) (mtEnv))))) (numV 1))


;; Since we have a mutable state (the likelihood) threaded through computation,
;; we define the v*s form to represent the combination of a value and state.
(define-type ValueXState
  [v*s (val SMC-Value?) (state number?)])


;; Convenience function so it's possible to do:
;; (define-values (v s) (v*s->values ...))
(define (v*s->values v*s) (values (v*s-val v*s) (v*s-state v*s)))



;; ==============================================================
;;                       TEST HELPERS
;; ==============================================================
;; NOTE: These helpers are used by the test suites. DO NOT MODIFY.

;;Turn a distribution into a canonical form
;;Makes testing work nicely
;;Only works on distributions of numV
;;canonical-dist: distV? -> distV?
(define (canonical-dist d)
  (distV (map numV (canonical-list (map numV-n (distV-values d)))))
  )

;;Helper for above
;;canonical-list: (listof number?) -> (listof number?)
(define (canonical-list l)
  (let* ([elements (remove-duplicates l)] ; all the unique elements
         [elements-counts (map
                           (lambda (e) (count (lambda (x) (equal? x e)) l))
                           elements)]  ;the count of those unique elements
         [elements-gcd (apply gcd elements-counts)] ; gcd of those counts
         [new-lists (map
                     (lambda (num source-count)
                       (make-list (/ source-count elements-gcd) num))
                     elements elements-counts)]
         )
    (sort (flatten new-lists) <)))

;;Helper to make tests a bit shorter
;;Parse and run a query, assuming it returns a distV of numV values
;;run : sexp -> SMC-Value?
(define (run expr)
  (local [(define wrappedExpr (wrap-in-builtins expr))
          (define interpResult (interp (desugar (parse wrappedExpr true))))
          (define result (v*s-val interpResult))
          (define state (v*s-state interpResult))]
    (if (distV? result)
        (v*s (canonical-dist result) state)
        (v*s result state))))

;; Helper for testing
;; tests an expression that evaluates to a distV of numV's or a non distV
(define-syntax-rule (test-gen sexp val state)
  (test (local [(define result (run sexp))
                (define v (v*s-val result))
                (define s (v*s-state result))]
          (cons v s))
        (cons val state)))

;; Helper for testing
;; tests an expression that evaluates to a distV of distV (2-layer distV)
(define-syntax-rule (test-nested sexp val state)
  (local [(define expected (cons val state))
          (define (compare-nested-dist l1 l2)
            (cond [(empty? l1) #t]
                  [else
                   (if (member (first l1) l2)
                       (compare-nested-dist (rest l1) (remove (first l1) l2))
                       #f)]))
          (define (show-failed-test result)
            (test (local [(define testcase sexp)]
                    result) expected))]
    (with-handlers ([exn:fail? (lambda (e) (show-failed-test e))])
      (local [(define result (interp (parse sexp)))
              (define v (v*s-val result))
              (define s (v*s-state result))]
        (if (not (= (length (distV-values v)) (length (distV-values val))))
            (show-failed-test (cons v s))
            (let* ([cv (distV (map (lambda (d)
                                     (if (distV? d) (canonical-dist d) d))
                                   (distV-values v)))]
                   [result (and (compare-nested-dist (distV-values cv)
                                                     (distV-values val))
                                (= state s))])
              (if result
                  (test #t #t)
                  (show-failed-test (cons v s)))))))))


;; ==========================================================
;;                           PARSE
;; ==========================================================

; Defined at top level ONLY for testing: "safe" replacement for modulo:
(define (internal-modulo n m)
  (if (zero? m)
      (error '% "Mod by zero in % ~a ~a" n m)
      (modulo n m)))

(test (internal-modulo 5 2) 1)
(test (internal-modulo 6 2) 0)
(test/exn (internal-modulo 3 0) "")

;; lookup-op : symbol -> (or procedure false)
;; Produce the procedure associated with symbol or false if there is none
(define (lookup-op op)
  (match op
    ['+ +]
    ['* *]
    ['- -]
    ['< <]
    ['> >]
    ['<= <=]
    ['>= >=]
    ['= =]
    ['% internal-modulo]
    [_ #f]))

(test (lookup-op 'foo) false)
(test (lookup-op '*) *)
(test (lookup-op '%) internal-modulo)  ; an unusual case

;; op-exists? : symbol -> boolean
;; return true if op is a binop in our language and false otherwise
(define (op-exists? op) (if (lookup-op op) #t #f))
(test (op-exists? '*) #t)
(test (op-exists? 'with) #f)


;; reserved? : symbol -> boolean
;; return true if word is a reserved word (i.e., a symbol unusable by
;; the end-user-programmer as an identifier name)
(define (reserved? word)
  (if (or
       (member word '(infer distribution uniform sample begin observe ifelse
                            with* rec-with cons empty first rest empty? list fun))
       (lookup-op word)
       (string-prefix? (symbol->string word) "_"))
      #t
      #f))

(test (reserved? '*) #t)
(test (reserved? 'with*) #t)
(test (reserved? 'foo) #f)
(test (reserved? '_) #t)
(test (reserved? '_anything) #t)

;; parse : s-exp [bool] -> S-SMC
;; Consumes an s-expression and generates the corresponding S-SMC (surface AST)
;; By default, reserved words are disallowed, but if given false, reserved words
;; may be identifiers. (Intended solely for internal use by the language!)
(define (parse sexp (allow-reserved? false))
  (local [(define (valid-id? id)
            (and (symbol? id) (or allow-reserved? (not (reserved? id)))))
          (define (valid-op? exp)
            (and (symbol? exp) (op-exists? exp)))
          ; Intentionally shadowing the main "parse" so allow-reserved? persists.
          (define (parse sexp)
            (match sexp
              [(? number?) (s-num sexp)]
              [(? string?) (s-str sexp)]
              [`{distribution ,exp} (s-distribution (parse exp))]
              [`{uniform ,lexp ,hexp} (s-uniform (parse lexp) (parse hexp))]
              [`{sample ,exp} (s-sample (parse exp))]
              [`{begin ,exprs ...} (s-begin (map parse exprs))]

              ;; DONE #1: Parse the observe expression.
              ;; You may use the handy quasiquote syntax in the other cases
              ;; nearby or any match syntax you prefer!
              ;;
              ;; Be sure to see the EBNF above, as the syntax for observe has
              ;; changed (as well as its semantics).

              [`{observe ,dist = ,refval} (s-observe (parse dist) (parse refval))]
              
              [`{,(? valid-op? op) ,lexp ,rexp}
               (s-binop (lookup-op op) (parse lexp) (parse rexp))]
              [`{ifelse ,cexp ,texp ,eexp}
               (s-ifelse (parse cexp) (parse texp) (parse eexp))]
              [`{with* {{,(? valid-id? ids) ,nexps}...} ,body}
               (s-with* ids (map parse nexps) (parse body))]
              [`{rec-with {,(? valid-id? fname) {,pnames ...} ,fbody} ,body}
               (s-rec-with fname pnames (parse fbody) (parse body))]
              [`{cons ,fexp ,rexp} (s-cons (parse fexp) (parse rexp))]
              [`empty (s-empty)]
              [`{first ,cexp} (s-first (parse cexp))]
              [`{rest ,cexp} (s-rest (parse cexp))]
              [`{empty? ,cexp} (s-is-empty (parse cexp))]
              [`{list ,exps ...} (s-list (map parse exps))]
              [`{fun {,pnames ...} ,body}
               (if (= (length (remove-duplicates pnames)) (length pnames))
                   (s-fun pnames (parse body))
                   (error 'parse "Duplicate parameter names in: ~a" sexp))]
              [`{,fexp ,aexps ...} (s-app (parse fexp) (map parse aexps))]
              [(? valid-id? id) (s-id id)]
              [_ (error 'parse "Unable to recognize expr: ~a" sexp)]
              ))]
    (parse sexp)))

(test (parse 1) (s-num 1))
(test (parse "hello") (s-str "hello"))
(test (parse "goodbye") (s-str "goodbye"))

(test (parse '{distribution 1}) (s-distribution (s-num 1)))

(test (parse '{uniform a b}) (s-uniform (s-id 'a) (s-id 'b)))

(test (parse '{sample 1}) (s-sample (s-num 1)))

(test (parse '{begin 1}) (s-begin (list (s-num 1))))
(test (parse '{begin 1 2 3 4})
      (s-begin (list (s-num 1) (s-num 2) (s-num 3) (s-num 4))))

(test (parse '{observe 1 = 2}) (s-observe (s-num 1) (s-num 2)))

(test (parse '{+ 1 2}) (s-binop + (s-num 1) (s-num 2)))
(test (parse '{<= 1 2}) (s-binop <= (s-num 1) (s-num 2)))
(test (parse '{% 1 2}) (s-binop internal-modulo (s-num 1) (s-num 2)))

(test (parse '{ifelse 1 2 3}) (s-ifelse (s-num 1) (s-num 2) (s-num 3)))

(test (parse '{with* {} 1}) (s-with* empty empty (s-num 1)))
(test (parse '{with* {{x 2} {y 3} {z 4}} 1})
      (s-with* '(x y z) (list (s-num 2) (s-num 3) (s-num 4)) (s-num 1)))

(test (parse '{rec-with {f {} 1} 2}) (s-rec-with 'f empty (s-num 1) (s-num 2)))
(test (parse '{rec-with {f {a b c} 1} 2})
      (s-rec-with 'f '(a b c) (s-num 1) (s-num 2)))

(test (parse '{cons 1 2}) (s-cons (s-num 1) (s-num 2)))

(test (parse 'empty) (s-empty))

(test (parse '{first 1}) (s-first (s-num 1)))
(test (parse '{rest 1}) (s-rest (s-num 1)))
(test (parse '{empty? 1}) (s-is-empty (s-num 1)))

(test (parse '{list}) (s-list empty))
(test (parse '{list 1 2 3}) (s-list (list (s-num 1) (s-num 2) (s-num 3))))

(test (parse '{fun {} 1}) (s-fun empty (s-num 1)))
(test (parse '{fun {a b c} 1}) (s-fun '(a b c) (s-num 1)))
(test/exn (parse '{fun {x x} 1}) "")
(test/exn (parse '{fun {a b c a d} 1}) "")

(test (parse '{1}) (s-app (s-num 1) empty))
(test (parse '{1 2 3 4}) (s-app (s-num 1) (list (s-num 2) (s-num 3) (s-num 4))))

(test (parse 'x) (s-id 'x))

(test/exn (parse '_nope) "")
(test/exn (parse 'ifelse) "")



;; Testing the second argument:
(test (parse '_nope true) (s-id '_nope))
(test (parse 'observe true) (s-id 'observe))
(test/exn (parse '_nope false) "")
(test/exn (parse 'observe false) "")



;; ==========================================================
;;                          DESUGAR
;; ==========================================================

;; DEFAULT RECURSIVE BINDINGS available as builtins.
;; List of lists, where each list contains three elements:
;; 1) The name of the function (a symbol), which CAN be reserved.
;; 2) The names of the parameters (symbols), which CANNOT be reserved.
;; 3) The body of the function (concrete syntax),
;;    which CANNOT use reserved identifiers EXCEPT the function names.
(define DEFAULT_BINDINGS
  (list
   (list '_range '(lo hi) '{ifelse {<= hi lo} empty {cons lo {_range {+ lo 1} hi}}})
   (list 'range '(lo hi) '{_range lo hi})
   (list '_nth '(lst pos) '{ifelse {<= pos 0} {first lst} {_nth {rest lst} {- pos 1}}})
   (list 'nth '(lst pos) '{_nth lst pos})))

;; wrap-in-builtins : any -> s-expr
;; Given a program body (a query), wraps it in the built-in functions and
;; returns the result. CHECKS FOR RESERVED WORDS AND SYNTACTICALLY CORRECT FORM
;; FIRST.
(define (wrap-in-builtins sexpr)
  (local [(define (wrap-body binding body)
            (wrap-body-split (first binding) (second binding) (third binding) body))
          (define (wrap-body-split fname params fbody body)
            `{rec-with {,fname ,params ,fbody} ,body})]
    ; Check for syntactic correctness:
    (parse (foldr (lambda (binding result)
                    (local [(define fname (first binding))
                            (define params (second binding))
                            (define fbody '1)]
                      (wrap-body-split fname params fbody result)))
                  sexpr
                  (filter (lambda (binding) (not (reserved? (first binding))))
                          DEFAULT_BINDINGS)))
    ; Do the actual wrapping. _STACK is inserted to support name stack desugaring.
    `{with* {{_STACK {list "root"}}} ,(foldr wrap-body sexpr DEFAULT_BINDINGS)}))

(test/exn (wrap-in-builtins '_range) "")
(test (wrap-in-builtins 'range)
      '{with* {{_STACK {list "root"}}}
              {rec-with {_range {lo hi} {ifelse {<= hi lo}
                                                empty
                                                {cons lo {_range {+ lo 1} hi}}}}
                        {rec-with {range {lo hi} {_range lo hi}}
                                  {rec-with {_nth {lst pos}
                                                  {ifelse
                                                   {<= pos 0}
                                                   {first lst}
                                                   {_nth {rest lst} {- pos 1}}}}
                                            {rec-with {nth {lst pos} {_nth lst pos}}
                                                      range}}}}})

;; desugar: S-SMC -> D-SMC
;; desugar the given program to its internal representation
(define (desugar s-ast)
  (type-case S-SMC s-ast
    [s-num (n) (d-num n)]
    [s-distribution (list-exp) (d-distribution (desugar list-exp))]

    ;; DONE #2: Desugar uniform. BE SURE TO READ the plan above in the
    ;; definition of D-SMC. In particular, note that the built-in function
    ;; _range will be handy. (It behaves exactly the same as the built-in
    ;; function range documented near the EBNF above.)
    [s-uniform (low high)
               (d-distribution (d-app (d-id '_range) (list (desugar low) (desugar high))))]
    
    [s-sample (dist-exp) (d-sample (desugar dist-exp))]
    [s-begin (exprs) (local [(define-values (first-exprs last-expr-list)
                               (split-at-right exprs 1))]
                       (desugar (s-with* (map (lambda (x) '_) first-exprs)
                                         first-exprs (first last-expr-list))))]
    [s-observe (dist val) (d-observe (desugar dist) (desugar val))]
    [s-binop (op lhs rhs) (d-binop op (desugar lhs) (desugar rhs))]
    [s-with* (names named-exprs body) (foldr (lambda (name named-exp result)
                                               (d-with name named-exp result))
                                             (desugar body)
                                             names
                                             (map desugar named-exprs))]
    [s-rec-with (fname params fbody body)
                (d-rec-with fname params (desugar fbody) (desugar body))]
    [s-ifelse (cond tbranch ebranch)
              (d-ifelse (desugar cond) (desugar tbranch) (desugar ebranch))]
    [s-cons (fst rst)
            (d-cons (desugar fst) (desugar rst))]
    [s-empty () (d-empty)]
    [s-first (exp) (d-first (desugar exp))]
    [s-rest (exp) (d-rest (desugar exp))]
    [s-is-empty (exp) (d-is-empty (desugar exp))]

    ;; TODO #3: Desugar list in terms of cons and empty. Again, note that
    ;; a strategy for the desugaring is described already at the definition of
    ;; D-SMC. You may also find it useful to look at the desugaring of s-with*
    ;; above, which is similar.
    [s-list (exps)
            (if (empty? exps)
                (d-empty)
                (d-cons (desugar (first exps)) (desugar (s-list (rest exps)))))]
    
    [s-fun (params body) (d-fun params (desugar body))]
    [s-app (function args) (d-app (desugar function) (map desugar args))]
    [s-id (name) (d-id name)]
    [s-str (s) (d-str s)]))

(test (desugar (parse 1)) (d-num 1))
(test (desugar (parse "abc")) (d-str "abc"))

(test (desugar (parse '{distribution 1})) (d-distribution (d-num 1)))

(test (desugar (parse '{uniform a b}))
      (d-distribution (d-app (d-id '_range) (list (d-id 'a) (d-id 'b)))))

(test (desugar (parse '{sample 1})) (d-sample (d-num 1)))

(test (desugar (parse '{begin 1})) (d-num 1))
(test (desugar (parse '{begin 1 2 3 4}))
      (desugar (s-with* (map (lambda (x) '_) (list (s-num 1) (s-num 2) (s-num 3)))
                        (list (s-num 1) (s-num 2) (s-num 3))
                        (s-num 4))))

(test (desugar (parse '{observe 1 = 2})) (d-observe (d-num 1) (d-num 2)))

(test (desugar (parse '{+ 1 2})) (d-binop + (d-num 1) (d-num 2)))
(test (desugar (parse '{<= 1 2})) (d-binop <= (d-num 1) (d-num 2)))
(test (desugar (parse '{% 1 2})) (d-binop internal-modulo (d-num 1) (d-num 2)))

(test (desugar (parse '{with* {} 1})) (d-num 1))
(test (desugar (parse '{with* {{x 2} {y 3} {z 4}} 1}))
      (d-with 'x (d-num 2)
              (d-with 'y (d-num 3)
                      (d-with 'z (d-num 4) (d-num 1)))))

(test (desugar (parse '{rec-with {f {} 1} 2}))
      (d-rec-with 'f empty (d-num 1) (d-num 2)))
(test (desugar (parse '{rec-with {f {a b c} 1} 2}))
      (d-rec-with 'f '(a b c) (d-num 1) (d-num 2)))

(test (desugar (parse '{ifelse 1 2 3})) (d-ifelse (d-num 1) (d-num 2) (d-num 3)))

(test (desugar (parse '{cons 1 2})) (d-cons (d-num 1) (d-num 2)))

(test (desugar (parse 'empty)) (d-empty))

(test (desugar (parse '{first 1})) (d-first (d-num 1)))
(test (desugar (parse '{rest 1})) (d-rest (d-num 1)))
(test (desugar (parse '{empty? 1})) (d-is-empty (d-num 1)))

(test (desugar (parse '{list})) (d-empty))
(test (desugar (parse '{list 1 2 3}))
      (d-cons (d-num 1) (d-cons (d-num 2) (d-cons (d-num 3) (d-empty)))))

(test (desugar (parse '{fun {} 1})) (d-fun empty (d-num 1)))
(test (desugar (parse '{fun {a b c} 1})) (d-fun '(a b c) (d-num 1)))

(test (desugar (parse '{1})) (d-app (d-num 1) empty))
(test (desugar (parse '{1 2 3 4}))
      (d-app (d-num 1) (list (d-num 2) (d-num 3) (d-num 4))))

(test (desugar (parse 'x)) (d-id 'x))





;; ==========================================================
;;                           INTERP
;; ==========================================================

;;wrapResult : (or boolean? number?) -> SMC-Value?
;;Helper function for turning the result of an operation into a numV
(define (wrapResult res)
  (cond
    [(boolean? res) (if res (numV 1) (numV 0))]
    [(number? res) (numV res)]
    [else (error "Binary operations should produce numbers or booleans")]))

;; (listof (Pair X number)) -> (listof X)
;; Normalizes a list of pairs of (X weight) to a list
(define (normalize-weighted-pairs lop)
  (local [(define GCD (apply gcd (map cdr lop)))]
    (flatten (map (match-lambda [(cons value weight)
                                 (build-list (inexact->exact (/ weight GCD))
                                             (lambda (n) value))])
                  lop))))

(test (normalize-weighted-pairs empty)
      empty)
(test (normalize-weighted-pairs (list (cons 'a 0.1)
                                      (cons 'b 0.2)))
      (list 'a 'b 'b))
(test (normalize-weighted-pairs (list (cons 'a 0.25)
                                      (cons 'b 0.75)))
      (list 'a 'b 'b 'b))
(test (normalize-weighted-pairs (list (cons 'a 0.25)
                                      (cons 'b 0.50)
                                      (cons 'c 0.125)))
      (list 'a 'a 'b 'b 'b 'b 'c))


;; assert-type : SMC-Value (SMC-Value -> bool) -> SMC-Value
;; If val passes pred, returns val. Else, produces an interpreter error.
(define (assert-type val pred)
  (when (not (pred val))
    (error 'interp "type error ~a should be ~a but is not" val pred))
  val)

(test (assert-type (numV 1) numV?) (numV 1))
(test (assert-type (numV 2) numV?) (numV 2))
(test (assert-type (emptyV) emptyV?) (emptyV))

(test/exn (assert-type (emptyV) numV?) "")
(test/exn (assert-type (numV 1) emptyV?) "")

;; assert-type-v*s : v*s (SMC-Value -> bool) -> v*s
;; like assert-type but works with a v*s and preserves its state
(define (assert-type-v*s v*s pred)
  (assert-type (v*s-val v*s) pred)
  v*s)


; Light testing, since it just hands off to above.
(test (assert-type-v*s (v*s (numV 1) 0.3) numV?) (v*s (numV 1) 0.3))
(test (assert-type-v*s (v*s (numV 2) 0.5) numV?) (v*s (numV 2) 0.5))
(test/exn (assert-type-v*s (v*s (numV 1) 0.3) emptyV?) "")




;; CPS UTILITY: foldl/k
;; Plus non-CPS version for testing.


;; TODO #4: There's a small error in this CPS-converted implementation
;; of foldl. You should be able to find it using just the my-foldl tests
;; below, not trying to debug its use in interp!

;; foldl/k : (X Y (Y -> ()) -> ()) Y (listof X) (Y -> ()) -> ()
;; A CPS version of foldl. If lst is (x1 x2 x3 ... xn), then
;; like (proc xn (proc xn-1 (proc xn-2 (proc ... (proc x1 init)))))
;; except computed efficiently (i.e., in tail-recursive form).
(define (foldl/k proc/k init lst k)
  (local [(define (helper/k lst acc k)
            (if (empty? lst)
                acc
                (proc/k
                 (first lst) acc
                 (lambda (p-res)
                   (helper/k (rest lst) p-res k)))))]
    (helper/k lst init k)))
(define (my-foldl proc init lst)
  (let/cc k
    (foldl/k (lambda (x acc k) (k (proc x acc))) init lst k)
    (error "Reached this point, which should not happen!")))

(test (my-foldl (lambda (x acc) (+ (* 10 acc) x)) 0 '(1 8 2 3)) 1823)
(test (my-foldl cons empty '("hello" "goodbye")) '("goodbye" "hello"))


;; interp : D-SMC [Env] [number] [Controller] [Sampler] -> ValueXState
;; This procedure interprets the given SMC and produces a result
;; in the form of a SMC-Value and a weight (a number representing
;; the probability) using a specifically seeded random number
;;
;; A Controller is a (escaper) function: v*s (v*s ->) NameStack ->
;; It is called at each observe, just before the observe returns
;; its result. The Controller's arguments are:
;; 1) The value and state slated to be returned from the observe
;; 2) The continuation of the observe (an escaper).
;; 3) The "name stack" including that observe (the function call
;;    stack leading to that observe in a so-far-unspecified format).
;;
;; The default controller is:
;; (lambda (result continuation name-stack) (continuation result))
;;
;; A Sampler takes a distV and returns one element of the distribution,
;; selected uniformly at random.
(define (interp expr (env (mtEnv)) (state 1)
                (controller (lambda (result continuation name-stack)
                              (continuation result)))
                (get-sample (get-default-sampler)))
  (let/cc k
    (interp/k expr env state k controller get-sample)
    (error 'interp "interp/k returned from evaluation of ~a" expr)))

(define (interp/k expr (env (mtEnv)) (state 1) (k (lambda (x) x))
                  (controller (lambda (result continuation name-stack)
                                (continuation result)))
                  (get-sample (get-default-sampler)))
  (local [;; We grab the ORIGINAL continuation of the top-level call to interp/k,
          ;; and when we want to reject, simply use IT as our continuation rather
          ;; than the current continuation. As a result, we just "shoot" right out
          ;; of the computation, skipping any remaining work. Cool, huh? :)
          ;;
          ;; Search for reject-k below to see it in action.
          (define reject-k k)
          (define interp/k (lambda args (error "CALL HELPER INSTEAD!!")))

          ; We assume all operations take constant stack space.
          ; So, no apply-op/k needed!
          (define (apply-op op lval rval)
            (local [(define result (op (numV-n lval) (numV-n rval)))]
              (numV (cond [(false? result) 0]
                          [(boolean? result) 1]
                          [else result]))))
          (define (helper/k expr env state k)
            (type-case D-SMC expr
              [d-num (n) (k (v*s (numV n) state))]
              [d-str (s) (k (v*s (stringV s) state))]
              [d-binop (op lhs rhs)
                       (helper/k
                        lhs env state
                        (lambda (lres)
                          (local [(define-values (lval lstate)
                                    (v*s->values (assert-type-v*s lres numV?)))]
                            (helper/k
                             rhs env lstate
                             (lambda (rres)
                               (local [(define-values (rval rstate)
                                         (v*s->values (assert-type-v*s rres numV?)))]
                                 (k (v*s (apply-op op lval rval) rstate))))))))]
              [d-with (name named-expr body)
                      ;; TODO #5: Implement with. Note that we've provided
                      ;; a non-CPS-converted implementation. So, convert it
                      ;; to CPS!
                      ;;
                      ;; Our tests don't ensure that you put the body in tail
                      ;; position.. but you should! And, you should know what
                      ;; it looks like for something to "be in tail position".
                      (error "d-with interpretation unimplemented")
                      #; ; non-CPS version:
                      (local [(define-values (neval nestate)
                                (v*s->values (helper named-expr env state)))]
                        (helper body (anEnv name neval env) nestate))]
              [d-id (id) (k (v*s (lookup id env) state))]
              [d-ifelse (ce te ee)
                        (helper/k
                         ce env state
                         (lambda (ce-res)
                           (local [(define-values (cval cstate)
                                     (v*s->values (assert-type-v*s ce-res numV?)))
                                   (define next-exp
                                     (if (not (= (numV-n cval) 0)) te ee))]
                             (helper/k next-exp env cstate k))))]
              ;; TODO #6: There are some small errors in the implementation of
              ;; d-cons. Find and fix them!
              ;;
              ;; The one causing the error "Reached this point,
              ;; which should not happen!" is probably the first to debug.
              ;; The other is both more minor and more subtle and has to do
              ;; with state threading and order of evaluation.
              ;;
              ;; You may want to come back for the second error later.
              [d-cons (fst rst)
                      (helper/k
                       rst env state
                       (lambda (r-res)
                         (local [(define-values (rval rstate) (v*s->values r-res))]
                           (helper/k
                            fst env rstate
                            (lambda (f-res)
                              (local [(define-values (fval fstate)
                                        (v*s->values f-res))]
                                (v*s (consV fval rval) fstate)))))))]
              [d-empty () (k (v*s (emptyV) state))]
              [d-first (e)
                       (helper/k
                        e env state
                        (lambda (e-res)
                          (local [(define-values (eval estate)
                                    (v*s->values (assert-type-v*s e-res consV?)))]
                            (k (v*s (consV-first eval) estate)))))]
              [d-rest (e)
                      (helper/k
                       e env state
                       (lambda (e-res)
                         (local [(define-values (eval estate)
                                   (v*s->values (assert-type-v*s e-res consV?)))]
                           (k (v*s (consV-rest eval) estate)))))]
              [d-is-empty (e)
                          (helper/k
                           e env state
                           (lambda (e-res)
                             (local [(define-values (eval estate)
                                       (v*s->values
                                        (assert-type-v*s e-res
                                                         (or/c consV? emptyV?))))]
                               (k (v*s (numV (if (emptyV? eval) 1 0)) estate)))))]
              
              ;; TODO #7: We are using the wrong continuation/state inside of d-fun.
              ;; Patch them up, and be sure you know why we use what we use!
              ;;
              ;; If you read carefully the plan below, you should be able to fix
              ;; this without needing the test cases.
              [d-fun (params body)
                     (k (v*s (closureV
                              (lambda (argvs call-state call-k)
                                ; When invoked, this closure:
                                ; 0) Checks the parameter list's length.
                                ; 1) Binds its parameters to its argument values in
                                ;    the environment current AT FUNCTION DEFINITION.
                                ; 2) Evaluates the body recursively in the state
                                ;    current AT FUNCTION CALL.
                                (when (not (= (length argvs) (length params)))
                                  (error
                                   'interp
                                   "arity mismatch: expected ~a args; received ~a; name stack ~a"
                                   (length params)
                                   (length argvs)
                                   (SMC-Value->racket (lookup '_STACK env))))
                                ; Note that we return TO THE CALL SITE, i.e., we use call-k, not k.
                                ; This call to foldr is fine within CPS; it does nothing interesting :)
                                (helper/k body (foldr anEnv env params argvs) state k)))
                             state))]
              [d-app (fe argexps)
                     ; Evaluate the function expression:
                     (helper/k
                      fe env state
                      ; Then, evaluate all the argument expressions:
                      (lambda (fe-res)
                        (local [(define-values (fval fstate)
                                  (v*s->values (assert-type-v*s fe-res closureV?)))]
                          ; Note that we use a foldl to evaluates "left-to-right".
                          ; A foldr evaluates "right-to-left". However, foldl gives
                          ; us the results backward; so, we reverse them.
                          (foldl/k
                           ; Evaluating each argument expression and building up
                           ; the values in a list and threading through the state.
                           (lambda (argexp argvs-cons-state k)
                             (helper/k
                              argexp env (cdr argvs-cons-state)
                              (lambda (arg-res)
                                (local [(define-values (aval astate)
                                          (v*s->values arg-res))]
                                  (k (cons (cons aval (car argvs-cons-state))
                                           astate))))))
                           ; Initially empty list of values and state of fstate.
                           (cons empty fstate)
                           ; We fold over argexps.
                           argexps
                           ; Once we have both the function and argument values:
                           (lambda (fold-res)
                             ; Extract the argument values and state.
                             (local [(define argvs-rev-cons-state fold-res)
                                     (define argvs (reverse (car argvs-rev-cons-state)))
                                     (define astate (cdr argvs-rev-cons-state))]
                               ; And finally actually APPLY the function:
                               ((closureV-proc fval) argvs astate k)))))))]
              [d-rec-with (fname params fbody body)
                          (local [(define new-env (anEnv fname (rejectedV) env))]
                            (helper/k
                             (d-fun params fbody) new-env state
                             (lambda (fun-res)
                               (local [(define-values (fval fstate)
                                         (v*s->values (assert-type-v*s fun-res closureV?)))]
                                 ; Create the circular reference:
                                 (set-anEnv-value! new-env fval)
                                 (helper/k body new-env fstate k)))))]
              [d-distribution (le)
                              (helper/k
                               le env state
                               (lambda (le-res)
                                 (local [(define-values (lval lstate)
                                           (v*s->values
                                            (assert-type-v*s
                                             le-res (or/c consV? emptyV?))))]
                                   (when (emptyV? lval)
                                     (error 'interp "empty distribution in ~a" expr))
                                   (local [(define (list-convert/k cv k)
                                             (cond [(emptyV? cv) (k empty)]
                                                   [(consV? cv) (list-convert/k
                                                                 (consV-rest cv)
                                                                 (lambda (rlst)
                                                                   (k (cons (consV-first cv) rlst))))]
                                                   ; malformed list!
                                                   [else (error 'interp "creating distribution from malformed list in ~a" expr)]))]
                                     (list-convert/k
                                      lval
                                      (lambda (lc-res)
                                        (k (v*s (distV lc-res) lstate))))))))]
              [d-sample (e)
                        (helper/k
                         e env state
                         (lambda (e-res)
                           (local [(define-values (eval estate)
                                     (v*s->values (assert-type-v*s e-res distV?)))]
                             (if (empty? (distV-values eval))
                                 (error 'interp "attempt to sample empty distribution in ~a" e)
                                 (k (v*s (get-sample (distV-values eval)) estate))))))]
              [d-observe (de ve)
                ;; First, we need to evaluate the distribution and value expressions.
                (helper/k
                 de env state
                 (lambda (de-val)
                   (local [(define-values (dval dstate)
                             (v*s->values (assert-type-v*s de-val distV?)))]
                     (helper/k
                      ve env dstate
                      (lambda (ve-val)
                        (local [(define-values (vval vstate) (v*s->values ve-val))]
                          ; Next, we need to check which vals in dval equal vval.
                          (local [; Pull the values out of the distribution.
                                  (define vals (distV-values dval))
                                  
                                  ; Get just the matching values.
                                  (define matching-vals
                                    (filter (lambda (v) (equal? v vval)) vals))
                                  
                                  ; The likelihood update
                                  (define passed-fraction
                                    (/ (length matching-vals) (length vals)))
                                  
                                  ; The final result. If passed-fraction = 0, reject.
                                  ; Else, update state by the fraction that passed.
                                  ; Since only one value can "survive", we collapse
                                  ;; to just that one value.
                                  (define result (if (= passed-fraction 0)
                                                     (v*s (rejectedV) 0)
                                                     (v*s (distV (list vval))
                                                          (* vstate passed-fraction))))]
                            ; Now, hand off to the controller,
                            ; but when we come back, reject if needed.
                            (controller
                             result
                             ;; TODO #8: This lambda is the core of our interpreter.
                             ;; It enables the "sequential Monte Carlo" approach by
                             ;; handing off ot the "controller" function a continuation
                             ;; representing the computation in progress. That computation
                             ;; should (1) check whether v*s is a rejected value or not
                             ;; and (2a) if so, reject using the continuation reject-k
                             ;; (notice that if we use reject-k and not k, then we
                             ;; "instantly" propagate the rejection out of the
                             ;; computation in progress; no messy threading through our
                             ;; whole interpreter!) and (2b) if v*s is not a rejected
                             ;; value, simply return it as the observe's result.
                             ;;
                             ;; Because this lambda is a continuation, if the SMC
                             ;; controller decides it wants to "clone" this computation
                             ;; many times, it can simply call this continuation many
                             ;; times. If it wants to discard this computation, it
                             ;; just doesn't call the continuation at all.
                             (lambda (v*s)
                               ; TODO: implement the body based on the notes above.
                               ; Our version is three lines long with fewer than
                               ; 60 non-whitespace characters. So, don't do too much!
                               (k v*s))
                             ; The name stack is internally named _STACK.
                             (SMC-Value->racket (lookup '_STACK env))))))))))]))]
    (helper/k expr env state k)))





;;;;;;;;;; INTERP TESTING WITHOUT CONTROLLER ;;;;;;;;;;;;;;;;;;;;;

(test-gen '1 (numV 1) 1)
(test-gen '2 (numV 2) 1)

(test-gen '"moo" (stringV "moo") 1)
(test-gen '"ba" (stringV "ba") 1)

(test-gen '{begin 1} (numV 1) 1)
(test-gen '{begin 1 2} (numV 2) 1)
(test-gen '{begin 1 2 3 4} (numV 4) 1)

(test-gen '{+ 10 100} (numV 110) 1)
(test-gen '{- 10 100} (numV -90) 1)
(test-gen '{* 10 100} (numV 1000) 1)

(test-gen '{< 10 100} (numV 1) 1)
(test-gen '{< 5 5} (numV 0) 1)
(test-gen '{< 3 2} (numV 0) 1)
(test-gen '{> 10 100} (numV 0) 1)
(test-gen '{> 5 5} (numV 0) 1)
(test-gen '{> 3 2} (numV 1) 1)
(test-gen '{= 10 100} (numV 0) 1)
(test-gen '{= 5 5} (numV 1) 1)
(test-gen '{= 3 2} (numV 0) 1)
(test-gen '{<= 10 100} (numV 1) 1)
(test-gen '{<= 5 5} (numV 1) 1)
(test-gen '{<= 3 2} (numV 0) 1)
(test-gen '{>= 10 100} (numV 0) 1)
(test-gen '{>= 5 5} (numV 1) 1)
(test-gen '{>= 3 2} (numV 1) 1)

(test-gen '{% 5 3} (numV 2) 1)
(test-gen '{% 6 3} (numV 0) 1)


(test/exn (run '{+ empty 100}) "")
(test/exn (run '{- empty 100}) "")
(test/exn (run '{* empty 100}) "")
(test/exn (run '{< empty 100}) "")
(test/exn (run '{> empty 100}) "")
(test/exn (run '{= empty 100}) "")
(test/exn (run '{<= empty 100}) "")
(test/exn (run '{>= empty 100}) "")
(test/exn (run '{% empty 3}) "")
(test/exn (run '{+ 100 empty}) "")
(test/exn (run '{- 100 empty}) "")
(test/exn (run '{* 100 empty}) "")
(test/exn (run '{< 100 empty}) "")
(test/exn (run '{> 100 empty}) "")
(test/exn (run '{= 100 empty}) "")
(test/exn (run '{<= 100 empty}) "")
(test/exn (run '{>= 100 empty}) "")
(test/exn (run '{% 3 empty}) "")


(test/exn (run '{% 3 0}) "")




(test-gen '{ifelse 0 10 20} (numV 20) 1)
(test-gen '{ifelse 1 10 20} (numV 10) 1)
(test-gen '{ifelse -1.3 10 20} (numV 10) 1)


(test-gen '{cons 1 2} (consV (numV 1) (numV 2)) 1)
(test-gen 'empty (emptyV) 1)
(test-gen '{first {cons 1 2}} (numV 1) 1)
(test/exn (run '{first empty}) "")
(test/exn (run '{first 1}) "")
(test-gen '{rest {cons 1 2}} (numV 2) 1)
(test/exn (run '{rest empty}) "")
(test/exn (run '{rest 1}) "")
(test-gen '{empty? {cons 1 2}} (numV 0) 1)
(test-gen '{empty? empty} (numV 1) 1)
(test/exn (run '{empty? 1}) "")
(test-gen '{list} (emptyV) 1)
(test-gen '{list 1 2 3}
          (consV (numV 1)
                 (consV (numV 2)
                        (consV (numV 3) (emptyV))))
          1)

; It's indecently hard to test function definition directly because of the
; builtins and the Racket closure-based representation of closureV's.
; So, we just skip it (but test them during function application).

; Identifier reference:
(test (interp (desugar (parse 'x)) (anEnv 'x (numV 10) (anEnv 'y (numV 20) (mtEnv))))
      (v*s (numV 10) 1))
(test (interp (desugar (parse 'y)) (anEnv 'x (numV 10) (anEnv 'y (numV 20) (mtEnv))))
      (v*s (numV 20) 1))

; Zero-argument application:
(test-gen '{{fun {} 1}} (numV 1) 1)
(test-gen '{{fun {} 2}} (numV 2) 1)
(test/exn (run '{{fun {x} 1}}) "")
(test/exn (run '{{fun {x} 2}}) "")

; multi-argument application, including that positional bindings work right:
(test-gen '{{fun {x y z} 1} 1 2 3} (numV 1) 1)
(test-gen '{{fun {x y z} 2} 1 2 3} (numV 2) 1)

(test-gen '{{fun {x y z} x} 1 2 3} (numV 1) 1)
(test-gen '{{fun {x y z} y} 1 2 3} (numV 2) 1)
(test-gen '{{fun {x y z} z} 1 2 3} (numV 3) 1)

(test/exn (run '{{fun {x y z} 1}}) "")
(test/exn (run '{{fun {x y z} 1 2}}) "")
(test/exn (run '{{fun {x y z} 1 2 3 4}}) "")


(test-gen '{with* {} 3} (numV 3) 1)
(test-gen '{with* {{x 1} {y 2}} {+ x y}} (numV 3) 1)


(test-gen '{rec-with {f {} 1} {f}} (numV 1) 1)

; Recursion doesn't break everything:
(test-gen '{rec-with {f {x} {ifelse {<= x 0} 10 {f {- x 1}}}} {f 0}} (numV 10) 1)
(test-gen '{rec-with {f {x} {ifelse {<= x 0} 10 {f {- x 1}}}} {f 3}} (numV 10) 1)

; Recursion really works:
(test-gen '{rec-with {f {x} {ifelse {= x 0} 0 {+ x {f {- x 1}}}}} {f 5}} (numV 15) 1)




(test/exn (run '{distribution 1}) "")  ; distribution values must be lists
(test/exn (run '{distribution empty}) "")  ; distribution values must be NON-EMPTY lists
(test-gen '{distribution {list 1}} (distV (list (numV 1))) 1)
(test-gen '{distribution {list 1 1}} (distV (list (numV 1))) 1)  ; b/c test-gen normalizes
(test-gen '{distribution {list 1 2 2 3}} (distV (list (numV 1) (numV 2) (numV 2) (numV 3))) 1)

; Malformed lists are ALSO errors:
(test/exn (run '{distribution {cons 1 2}}) "")

(test/exn (run '{uniform 1 0}) "")  ; empty distributions produce errors
(test-gen '{uniform 3 8} (distV (list (numV 3) (numV 4) (numV 5) (numV 6) (numV 7))) 1)

(test-gen '{sample {distribution {list 1}}} (numV 1) 1)
(test-gen '{sample {distribution {list 1 1}}} (numV 1) 1)

(test-gen '{observe {uniform 0 5} = 3}
          (distV (list (numV 3)))
          (/ 1 5))
(test-gen '{observe {distribution {list 1 1 1 1 1}} = 1}
          (distV (list (numV 1)))
          1)
(test-gen '{observe {distribution {list 1 1 1 1 2}} = 1}
          (distV (list (numV 1)))
          (/ 4 5))
(test-gen '{observe {uniform 0 5} = 7} (rejectedV) 0)  ; no empty distributions

(test/exn (run '{observe 1 = {fun {x} 1}}) "") ; first value must be a distro


;; Built-in functions
(test-gen '{range 4 8}
          (consV (numV 4) (consV (numV 5) (consV (numV 6) (consV (numV 7) (emptyV)))))
          1)
(test-gen '{range 4 3} (emptyV) 1)
(test-gen '{nth {list 2 4 5 6} 2} (numV 5) 1)
(test-gen '{nth {list 2 4 5 6} 0} (numV 2) 1)



;;;;;;;;;;;;; Rejection propagation tests ;;;;;;;;;;;;;;;;;;;

;; Tests BOTH rejection propagation AND order of evaluation.
;; Note that to perform this testing, we need to provide a value for _STACK,
;; since observe assumes it exists.

; Expressions that when evaluated give: a distribution, a rejected value,
; and an error, plus the rejected value (plus state) itself and a starter env.
(define DIS (d-distribution (d-cons (d-num 1) (d-empty))))
(define REJ (d-observe DIS (d-fun '(x) (d-num 0))))
(define ERR (d-app (d-num 1) empty))
(define REJV (v*s (rejectedV) 0))
(define ENV (anEnv '_STACK (emptyV) (mtEnv)))

(test (interp (d-distribution REJ) ENV) REJV)
(test (interp (d-distribution (d-cons REJ ERR)) ENV) REJV)
(test/exn (interp (d-distribution (d-cons ERR REJ)) ENV) "")
(test (interp (d-distribution (d-cons (d-num 1) REJ)) ENV) REJV)

(test (interp (d-sample REJ) ENV) REJV)

(test (interp (d-observe REJ ERR) ENV) REJV)
(test/exn (interp (d-observe ERR REJ) ENV) "")
(test (interp (d-observe DIS REJ) ENV) REJV)

(test (interp (d-binop + REJ ERR) ENV) REJV)
(test/exn (interp (d-binop + ERR REJ) ENV) "")
(test (interp (d-binop + (d-num 1) REJ) ENV) REJV)

(test (interp (d-with 'x REJ ERR) ENV) REJV)
(test/exn (interp (d-with 'x ERR REJ) ENV) "")
(test (interp (d-with 'x DIS REJ) ENV) REJV)

(test (interp (d-rec-with 'f '(x) ERR REJ) ENV) REJV)
(test/exn (interp (d-rec-with 'f '(x) REJ ERR) ENV) "")
(test (interp (d-rec-with 'f '(x) REJ (d-num 1)) ENV) (v*s (numV 1) 1))
(test (interp (d-rec-with 'f empty REJ
                          (d-binop + (d-app (d-id 'f) empty) ERR)) ENV) REJV)

(test (interp (d-ifelse REJ ERR ERR) ENV) REJV)
(test/exn (interp (d-ifelse ERR REJ REJ) ENV) "")
(test (interp (d-ifelse (d-num 0) REJ (d-num 1)) ENV) (v*s (numV 1) 1))
(test (interp (d-ifelse (d-num 1) REJ (d-num 1)) ENV) REJV)
(test (interp (d-ifelse (d-num 1) (d-num 1) REJ) ENV) (v*s (numV 1) 1))
(test (interp (d-ifelse (d-num 0) (d-num 1) REJ) ENV) REJV)

(test (interp (d-cons REJ ERR) ENV) REJV)
(test (interp (d-cons DIS REJ) ENV) REJV)
(test/exn (interp (d-cons ERR REJ) ENV) "")

(test (interp (d-first REJ) ENV) REJV)
(test (interp (d-rest REJ) ENV) REJV)
(test (interp (d-is-empty REJ) ENV) REJV)

(test (interp (d-app REJ (list ERR)) ENV) REJV)
(test/exn (interp (d-app ERR (list REJ)) ENV) "")
(test/exn (interp (d-app (d-fun empty REJ) (list DIS)) ENV) "")
(test (interp (d-app (d-fun '(x) REJ) (list DIS)) ENV) REJV)
(test (interp (d-app (d-fun '(x y z) (d-id 'z)) (list DIS REJ DIS)) ENV) REJV)
(test/exn (interp (d-app (d-fun '(x y z) (d-id 'z)) (list DIS ERR REJ)) ENV) "")





;;;;;;;;;;;;;; State threading testing infrastructure ;;;;;;;;;;;;;;;;;;;;;;
;;
;; YOU MAY COMPLETELY IGNORE!
;;
;; We exploit the "callback" offered by the controller to test state threading.
;; Basically, we create a framework that "peeks" at the state as we go along
;; so we can tell if the interim (and not just final) states are correct.
;;
;; We play some minor number theoretical games to encode all the information we
;; want into the single number of the state. If you're familiar with it, we
;; basically use Godel numbering. If you're not.. doesn't matter :)

(define ST-PRIMES (next-primes 1 100))
(define ST-RESULT empty) ; stores the result of state threading tests during testing

;; A Controller (see interp's documentation) designed to test that we're threading state
;; correctly. Testing here relies on a sufficiently long list of primes in ST-PRIMES
;;
;; The controller detects which prime is in the distribution value.
;; Then, it finds all the prime indexes "hidden" in the state and their counts (via
;; prime factorization).
;;
;; If the distribution was NOT produced with a (known) prime, then index will be #f.
;;
;; When used, this will record one result on each observe.
(define (st-controller result continuation name-stack)
  (local [(define-values (val state) (v*s->values result))
          (define prime (floor (numV-n (first (distV-values val)))))
          (define index (index-of ST-PRIMES prime))
          (define state-indexes
            (map (match-lambda [(cons prime count)
                                (cons (index-of ST-PRIMES prime) count)])
                 (factorize (/ 1 state))))]
    ; Record which observe this was and what its inverted state was.
    (set! ST-RESULT (cons (cons index state-indexes) ST-RESULT))
    (continuation result)))

;; Creates code (in the end-user programming language) that creates
;; a distribution containing numbers between the index'th prime and the
;; next natural number (but less than that number). It wraps that distribution
;; in an observe that selects the prime and produces the given value expression.
(define (st-inject index (val-expr 0))
  (local [(define prime (list-ref ST-PRIMES index))
          (define dist-vals (build-list prime (lambda (n) (+ prime (/ n prime)))))]
    `{begin {observe
             {distribution {list ,@dist-vals}} =
             ,prime}
            ,val-expr}))

;; Initializes the global result list to empty then runs the program
;; using the st-controller and produces the results.
(define (st-run expr)
  (set! ST-RESULT empty)
  (local [(define wrappedExpr (wrap-in-builtins expr))]
    (interp (desugar (parse wrappedExpr true)) (mtEnv) 1 st-controller))
  (reverse ST-RESULT))


;;;;;;;;;;;;;; State threading tests ;;;;;;;;;;;;;;;;;;;;;;
(test (st-run `{distribution ,(st-inject 0 '{list 1})})
      ; One injection with index 0 run once. Should record just
      ; that index with a state reflecting that index:
      (list '(0 (0 1))))

(test (st-run `{uniform ,(st-inject 0 0) ,(st-inject 1 5)})
      ; Should run each just once, left-to-right:
      (list '(0 (0 1))
            '(1 (0 1) (1 1))))

(test (st-run `{sample ,(st-inject 0 '{uniform 0 1})})
      (list '(0 (0 1))))

(test (st-run `{begin ,(st-inject 0)
                      ,(st-inject 1)
                      ,(st-inject 2)})
      ; We can tell with this test that 0 went first, then 1, then 2.
      ; Further, the state was modified correctly along the way.
      (list '(0 (0 1))
            '(1 (0 1) (1 1))
            '(2 (0 1) (1 1) (2 1))))

(test (st-run
       `{observe ,(st-inject 0 '{distribution {list 0 1 0 0 4}}) =
                 ,(st-inject 1 1)})
      ; We get an observe on the 0, on the 1, and then we get the
      ; "natural" observe, which filters its distro down to 1/5 of
      ; the original set, and therefore adds a 2 index (the number
      ; 5).
      (list '(0 (0 1))
            '(1 (0 1) (1 1))
            '(#f (0 1) (1 1) (2 1))))

(test (st-run `{+ ,(st-inject 0) ,(st-inject 1)})
      (list '(0 (0 1))
            '(1 (0 1) (1 1))))

(test (st-run `{ifelse ,(st-inject 0 0) ,(st-inject 1) ,(st-inject 2)})
      (list '(0 (0 1))
            '(2 (0 1) (2 1))))


;;;;;;;;;;;;; Sampling (without infer-based resampling) ;;;;;;;;;;;;;;;

;; Sampling tests with no resampling via infer.
;; FIXED to our current random number generator!
(test-gen '{sample {uniform 0 2}} (numV 1) 1)
(test-gen '{sample {uniform 0 10}} (numV 8) 1)
(test-gen '{sample {uniform 0 888}} (numV 794) 1)




;; name-stack-xform : D-SMC -> D-SMC
;; Given an AST, produces a new AST in which each observe and each function application
;; has a unique "address", and the program maintains a call stack of sorts consisting
;; of these addresses. We call this the "name stack" or (internally) _STACK.
;;
;; Thus, every function must have an extra argument named _STACK, and every function
;; application must augment _STACK by cons'ing on its name and passing the result into
;; the function. observes must also have a name, which is awkward, since they shouldn't
;; push the name when evaluating their distro or predicate expressions. So, we wrap the
;; observe in bindings that front-load the distro and predicate evaluations and only then
;; update _STACK.
;;
;; Like this entire language, interpreter, and infenrence engine, this transformation,
;; is based on work by van de Meent et al, with particular thanks to Frank Wood.
;; See https://arxiv.org/pdf/1809.10756.pdf#page=164. Any problems in the nonsense we
;; actually do are purely our fault!
;;
;; TODO #9: This should name function applications with an ID expression in the function
;; expression position based on that ID using the helper function gen-name. However,
;; it doesn't do that now. Patch it in the d-app case.
(define (name-stack-xform d-ast)
  (local [(define name-stack-xform (lambda args (error "Don't call me. Call helper!!")))

          (define next-num 1)

          ; Generate a "fresh" name based on the given name.
          (define (gen-name name)
            (when (symbol? name)
              (set! name (symbol->string name)))
            (local [(define num next-num)]
              (set! next-num (add1 next-num))
              (string-append name "-" (number->string num))))
          
          (define (helper d-ast)
            (type-case D-SMC d-ast
              [d-num (n) (d-num n)]
              [d-distribution (e) (d-distribution (helper e))]
              [d-sample (e) (d-sample (helper e))]
              [d-binop (op le re) (d-binop op (helper le) (helper re))]
              [d-with (id ne body) (d-with id (helper ne) (helper body))]
              [d-ifelse (c t e) (d-ifelse (helper c) (helper t) (helper e))]
              [d-cons (fe re) (d-cons (helper fe) (helper re))]
              [d-empty () (d-empty)]
              [d-first (e) (d-first (helper e))]
              [d-rest (e) (d-rest (helper e))]
              [d-is-empty (e) (d-is-empty (helper e))]
              [d-id (n) (d-id n)]
              [d-str (s) (d-str s)]
              [d-rec-with (fname params fbody body)
                (d-rec-with fname (cons '_STACK params) (helper fbody) (helper body))]
              ; Pre-evaluate the distribution and predicate expressions, then
              ; put a new name on the stack for this observe, and only then actually
              ; do the observe.
              [d-observe (de pe)
                (d-with '_DVAL (helper de)
                        (d-with '_PVAL (helper pe)
                                (d-with '_STACK (d-cons (d-str (gen-name "observe"))
                                                        (d-id '_STACK))
                                        (d-observe (d-id '_DVAL) (d-id '_PVAL)))))]
              [d-fun (params body) (d-fun (cons '_STACK params) (helper body))]
              [d-app (fe aes)
                     (local [(define name (gen-name "anon"))]
                       (d-app (helper fe)
                              (cons (d-cons (d-str name) (d-id '_STACK))
                                    (map helper aes))))]))]
    (helper d-ast)))


; "Normal" tests. Nothing special happens. These don't really test that we RECURSIVELY
; perform the xform. See below for that.
;
; Note that many of these tests are runtime errors but are no problem for a static transform.
(test (name-stack-xform (d-num 1)) (d-num 1))
(test (name-stack-xform (d-distribution (d-num 1))) (d-distribution (d-num 1)))
(test (name-stack-xform (d-sample (d-num 1))) (d-sample (d-num 1)))
(test (name-stack-xform (d-binop + (d-num 1) (d-num 2))) (d-binop + (d-num 1) (d-num 2)))
(test (name-stack-xform (d-with 'x (d-num 1) (d-num 2))) (d-with 'x (d-num 1) (d-num 2)))
(test (name-stack-xform (d-ifelse (d-num 1) (d-num 2) (d-num 3)))
      (d-ifelse (d-num 1) (d-num 2) (d-num 3)))
(test (name-stack-xform (d-cons (d-num 1) (d-num 2))) (d-cons (d-num 1) (d-num 2)))
(test (name-stack-xform (d-empty)) (d-empty))
(test (name-stack-xform (d-first (d-num 1))) (d-first (d-num 1)))
(test (name-stack-xform (d-rest (d-num 1))) (d-rest (d-num 1)))
(test (name-stack-xform (d-is-empty (d-num 1))) (d-is-empty (d-num 1)))
(test (name-stack-xform (d-id 'x)) (d-id 'x))
(test (name-stack-xform (d-str "hello")) (d-str "hello"))

; Now, the only interesting cases:

; Prepare to receive names:
(test (name-stack-xform (d-rec-with 'f (list 'x 'y) (d-num 1) (d-num 2)))
      (d-rec-with 'f (list '_STACK 'x 'y) (d-num 1) (d-num 2)))
(test (name-stack-xform (d-fun (list 'x 'y) (d-num 1)))
      (d-fun (list '_STACK 'x 'y) (d-num 1)))

; Prepare to update names:
(test (name-stack-xform (d-observe (d-num 1) (d-num 2)))
      (d-with '_DVAL (d-num 1)
              (d-with '_PVAL (d-num 2)
                      (d-with '_STACK (d-cons (d-str "observe-1") (d-id '_STACK))
                              (d-observe (d-id '_DVAL) (d-id '_PVAL))))))

; When we have an ID for a function, use that name:
(test (name-stack-xform (d-app (d-id 'here-is-a-name) (list (d-num 1) (d-num 2))))
      (d-app (d-id 'here-is-a-name)
             (list (d-cons (d-str "here-is-a-name-1") (d-id '_STACK)) (d-num 1) (d-num 2))))
; Else, just use anon:
(test (name-stack-xform (d-app (d-num 3) (list (d-num 1) (d-num 2))))
      (d-app (d-num 3) (list (d-cons (d-str "anon-1") (d-id '_STACK)) (d-num 1) (d-num 2))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sequential Monte Carlo inference engine
;;
;; There are no "TODOs" in this section, and the exam won't cover it.. but
;; this is also the coolest part. This is where we get payoff from all the work
;; above by supplying a controller that can weigh the value of the different
;; computations-in-progress provided at observes (i.e., breakpoints) and choose
;; which to replicate and which to discard.

;; parse-program: any -> S-Program
;; parse the given program in concrete syntax into its surface AST representation
;; INCLUDES wrapping in builtins.
(define (parse-program sexp)
  (match sexp
    [`{infer ,(? exact-positive-integer? n) ,query}
     (s-program n (parse (wrap-in-builtins query) true))]
    [_ (error 'parse-program "given ~a not {infer <positive> <SMC>}" sexp)]))

(test (parse-program '{infer 4 10})
      (s-program 4 (parse (wrap-in-builtins '10) true)))


;; desugar-program: S-Program -> D-Program
;; desugar the given program
(define (desugar-program s-ast)
  (type-case S-Program s-ast
    [s-program (n query)
               (d-program n (desugar query))]))

(test (desugar-program (parse-program '{infer 4 10}))
      (d-program 4 (desugar (parse (wrap-in-builtins '10) true))))


;; A pending computation returned by an observe in the midst of interpretation
;; (or a final result).
(define-type PendingComputation
  ; A computed computation will: false for the continuation, an empty name stack,
  ; and the interim result will actually be its final result.
  [pc (continuation (or/c procedure? false?)) ; remaining computation to be performed
      (interim-result ValueXState?)           ; computation result at its last breakpoint
      (name-stack (listof string?))])         ; function call stack (+ observe name)





;; Convenience accessors for the value/state out of a pending computation.
(define (get-value-pc pc)
  (v*s-val (pc-interim-result pc)))
(define (get-state-pc pc)
  (v*s-state (pc-interim-result pc)))

(test (get-value-pc (pc (lambda (x) x) (v*s (numV 1) 0.4) empty)) (numV 1))
(test (get-value-pc (pc (lambda (x) x) (v*s (numV 3) 0.24) empty)) (numV 3))
(test (get-state-pc (pc (lambda (x) x) (v*s (numV 1) 0.4) empty)) 0.4)
(test (get-state-pc (pc (lambda (x) x) (v*s (numV 3) 0.24) empty)) 0.24)


;; get-total-state : (listof PendingComputation) -> number
;; return the total of the states in pcs
(define (get-total-state pcs)
  (foldl + 0 (map get-state-pc pcs)))

(test (get-total-state empty) 0)
(test (get-total-state (list (pc identity (v*s (numV 1) 0.4) empty)
                             (pc identity (v*s (numV 3) 0.24) empty)))
      (+ 0.4 0.24))


;; Convenience function to replace the state in a pending computation
;; New state defaults to 1.
(define (reweight-pc pcomp (s 1))
  (type-case PendingComputation pcomp
    [pc (cont result name-stack)
        (pc cont (v*s (v*s-val result) s) name-stack)]))

; Two separate (lambda (x) x)'s do not compare equal, but identity compares equal to itself. 
(test (reweight-pc (pc identity (v*s (numV 1) 0.4) empty))
      (pc identity (v*s (numV 1) 1) empty))
(test (reweight-pc (pc identity (v*s (numV 1) 0.4) empty) 0.5)
      (pc identity (v*s (numV 1) 0.5) empty))



;; normalize-pcs : (listof PendingComputation) -> (listof PendingComputation)
;; Normalize the states in the computation results (so they sum to one).
(define (normalize-pcs pcs)
  (local [(define total (get-total-state pcs))]
    (map (lambda (pc) (reweight-pc pc (/ (get-state-pc pc) total))) pcs)))

(test (normalize-pcs empty) empty)
(test (normalize-pcs (list (pc identity (v*s (numV 1) 0.4) empty)
                           (pc identity (v*s (numV 3) 0.24) empty)))
      (list (pc identity (v*s (numV 1) (/ 0.4 0.64)) empty)
            (pc identity (v*s (numV 3) (/ 0.24 0.64)) empty)))


;; find-pc : (listof pc) number number
;; Produces the first pc in pcs such that the total state up
;; to and including that pc is greater than target.
;; I.e., suitable for randomly sampling a pc from pcs respecting
;; the likelihoods.
;;
;; Assumes: pcs is non-empty, (get-total-state pcs) > target,
;; 0 <= target.
;;
;; Aside: this could be more efficient via:
;; 1) Pre-compute the "prefix sums" of the states up to j for
;;    every j in range [0, n). (Once for all samples.)
;; 2) Binary search for the smallest prefix sum that is greater than
;;    a random number drawn from [0, 1). (Once for each sample.)
(define (find-pc pcs target)
  (cond
    [(= (length pcs) 1) (first pcs)]
    [(> (get-state-pc (first pcs)) target) (first pcs)]  ; got enough state!
    [else (find-pc (rest pcs) (- target (get-state-pc (first pcs))))])) ; keep looking

(test (find-pc (list (pc identity (v*s (numV 1) 0.4) empty)) 0)
      (pc identity (v*s (numV 1) 0.4) empty))
(test (find-pc (list (pc identity (v*s (numV 1) 0.4) empty)
                     (pc identity (v*s (numV 3) 0.24) empty)) 0)
      (pc identity (v*s (numV 1) 0.4) empty))
(test (find-pc (list (pc identity (v*s (numV 1) 0.4) empty)
                     (pc identity (v*s (numV 3) 0.24) empty)) 0.399)
      (pc identity (v*s (numV 1) 0.4) empty))
(test (find-pc (list (pc identity (v*s (numV 1) 0.4) empty)
                     (pc identity (v*s (numV 3) 0.24) empty)) 0.4)
      (pc identity (v*s (numV 3) 0.24) empty))
(test (find-pc (list (pc identity (v*s (numV 1) 0.8) empty)
                     (pc identity (v*s (numV 1) 0.4) empty)
                     (pc identity (v*s (numV 3) 0.24) empty)) 1)
      (pc identity (v*s (numV 1) 0.4) empty))

;; resample-all-computations : (listof pc) number -> (listof pc)
;; Produce a new set of computations of length n---each with state 1---
;; by sampling respecting the likelihoods of the pcs.
;;
;; n must be a positive integer. If not provided, defaults to (length pcs).
;; The total state of pcs must be positive.
(define (resample-all-computations pcs (n (length pcs)))
  (local [(define total (get-total-state pcs))
          (define (sample-pc ignore) (reweight-pc (find-pc pcs (* (random) total))))]
    (build-list n sample-pc)))

; Slightly tricky to test!
(test/pred (resample-all-computations (list (pc identity (v*s (numV 1) 0.8) empty)
                                            (pc identity (v*s (numV 1) 0.4) empty)
                                            (pc identity (v*s (numV 3) 0.24) empty)) 1)
           (lambda (x) (and (= 1 (length x))
                            (member (first x) (list (pc identity (v*s (numV 1) 1) empty)
                                                    (pc identity (v*s (numV 1) 1) empty)
                                                    (pc identity (v*s (numV 3) 1) empty))))))
(test (resample-all-computations (list (pc identity (v*s (numV 1) 0.8) empty)) 4)
      (list (pc identity (v*s (numV 1) 1) empty)
            (pc identity (v*s (numV 1) 1) empty)
            (pc identity (v*s (numV 1) 1) empty)
            (pc identity (v*s (numV 1) 1) empty)))
(test/pred (resample-all-computations (list (pc identity (v*s (numV 1) 0.8) empty)
                                            (pc identity (v*s (numV 1) 0.4) empty)
                                            (pc identity (v*s (numV 3) 0.24) empty)))
           (lambda (x)
             (and (= (length x) 3)
                  (andmap (lambda (x)
                            (member x (list (pc identity (v*s (numV 1) 1) empty)
                                            (pc identity (v*s (numV 1) 1) empty)
                                            (pc identity (v*s (numV 3) 1) empty))))
                          x))))


;; computation-complete? : pcs -> bool
;; true iff all computation results have empty name stacks
(define (computation-complete? pcs)
  (andmap (compose empty? pc-name-stack) pcs))

(test (computation-complete? empty) true)
(test (computation-complete? (list (pc identity (v*s (emptyV) 1) empty))) true)
(test (computation-complete? (list (pc identity (v*s (emptyV) 1) '("a")))) false)
(test (computation-complete? (list (pc identity (v*s (emptyV) 1) empty)
                                   (pc identity (v*s (emptyV) 1) '("a"))
                                   (pc identity (v*s (emptyV) 1) empty))) false)
(test (computation-complete? (list (pc identity (v*s (emptyV) 1) empty)
                                   (pc identity (v*s (emptyV) 1) empty)
                                   (pc identity (v*s (emptyV) 1) empty))) true)


;; validate-results : (listof pc) -> (listof pc)
;; Produces an error if any two computations in pcs have different name-stacks.
;; Otherwise, just returns the same list.
(define (validate-results pcs)
  (if (or (empty? pcs)
          (local [(define ref-name-stack (pc-name-stack (first pcs)))]
            (andmap (lambda (pc) (equal? (pc-name-stack pc) ref-name-stack)) pcs)))
      pcs
      (error 'validate-results "Computations stopped at different places in ~a" pcs)))

(test (validate-results empty) empty)
(test (validate-results (list (pc identity (v*s (emptyV) 1) empty)
                              (pc identity (v*s (emptyV) 1) empty)
                              (pc identity (v*s (emptyV) 1) empty)))
      (list (pc identity (v*s (emptyV) 1) empty)
            (pc identity (v*s (emptyV) 1) empty)
            (pc identity (v*s (emptyV) 1) empty)))
(test (validate-results (list (pc identity (v*s (emptyV) 1) '("1" "2" "1"))
                              (pc identity (v*s (emptyV) 1) '("1" "2" "1"))
                              (pc identity (v*s (emptyV) 1) '("1" "2" "1"))))
      (list (pc identity (v*s (emptyV) 1) '("1" "2" "1"))
            (pc identity (v*s (emptyV) 1) '("1" "2" "1"))
            (pc identity (v*s (emptyV) 1) '("1" "2" "1"))))
(test/exn (validate-results (list (pc identity (v*s (emptyV) 1) '("1" "2" "1"))
                                  (pc identity (v*s (emptyV) 1) '("1" "2"))
                                  (pc identity (v*s (emptyV) 1) '("1" "2" "1")))) "")


;; Collect the results of inference in a reasonable form.
(define (collect-results pcs)
  (local [(define result (make-hash))]
    (for ([comp pcs])
      (type-case ValueXState (pc-interim-result comp)
        [v*s (val state)
             (hash-update! result val (lambda (s) (+ s state)) 0)]))
    (hash->list result)))

(test (collect-results empty) empty)
(test (sort (collect-results (list (pc identity (v*s (numV 2) 1) empty)
                                   (pc identity (v*s (numV 4) 1) empty)
                                   (pc identity (v*s (numV 2) 1) empty)))
            (lambda (x y) (< (numV-n (car x)) (numV-n (car y)))))
      (sort (list (cons (numV 2) 2) (cons (numV 4) 1))
            (lambda (x y) (< (numV-n (car x)) (numV-n (car y))))))



;; A cheesy way to track the continuation used by our controllers.
;; If you wanted to manage this in parallel, you'd probably use a
;; vector with one entry for each particle in inference (or at least
;; for each thread). (You'd also want vector(s) for the pending
;; computations and computation results so that each thread can
;; update its results without interfering with the other threads.)
(define *CBOX* (box false))

;; Create a "controller" to pass to interp when starting an SMC-based computation.
;; If you wanted to parallelize, you'd probably want an integer parameter here for
;; WHICH controller this is. You'd then refer to a vector of (mutable) continuations
;; to invoke when the controller is called rather than to a single, global continuation.
(define (make-smc-controller boxed-continuation)
  (lambda (result continuation name-stack)
    ((unbox boxed-continuation) (pc continuation result name-stack))))

(test ((make-smc-controller (box identity)) (v*s (numV 1) 0.5) max empty)
      (pc max (v*s (numV 1) 0.5) empty))
; Check that we can "mess with" what's in the box and the controller will access it.
(test (local [(define b (box identity))
              (define controller (make-smc-controller b))]
        (set-box! b (lambda (pc) (list (pc-interim-result pc)
                                       (pc-name-stack pc)
                                       (pc-continuation pc))))
        (controller (v*s (numV 3) 0.2) identity '("a")))
      (list (v*s (numV 3) 0.2) '("a") identity))
     

;; D-Program -> (listof (cons SMC-Value likelihood))
;; Perform sequential monte carlo inference over the given program.
(define (infer-smc d-ast)
  ;; Note that much of the "plumbing" here would change to be indexed by WHICH
  ;; computation (indexed by number) was running for a parallel implementation.
  (type-case D-Program d-ast
    [d-program (n raw-query)
               (local [;; Do the name stack transform so that we can check that 
                       ;; computations always halt at the same observe.
                       (define query (name-stack-xform raw-query))

                       ;; A sampler (so we don't get the same results on every run of infer!).
                       (define sampler (get-default-sampler))

                       ;; A box containing the continuation to use for all controllers.
                       ;; And the one controller to use for all computations. 
                       (define CBOX (box false))
                       (define controller (make-smc-controller CBOX))

                       ;; () -> pc
                       ;; Initialize one computation, ready to start interpretation.
                       ;; Does NOT actually start it running!
                       ;; The initial value is arbitrary and unused. The initial
                       ;; state is the state used on the first call to interp.
                       ;; It should be 1 normally. The initial name-stack is
                       ;; arbitrary and unused.
                       (define (initialize-computation)
                         (pc
                          (lambda (val-state)
                            ; Initial computation runs interp and registers the controller.
                            ; Subsequent computations re-enter the interpretation in
                            ; progress. When interpretation FINISHES, that also hands
                            ; off to the controller, but using an empty name-stack to
                            ; flag that it is complete.
                            (controller (interp query (mtEnv) (v*s-state val-state)
                                                controller sampler)
                                        false
                                        empty))
                          (v*s (numV 0) 1)
                          empty))
              
                       ;; Initialize ALL pending computations.
                       (define (initialize-all-computations)
                         (build-list n (lambda (x) (initialize-computation))))

                       ;; Resume the computation pc and instruct it (via the controller)
                       ;; to return to this call to resume when complete.
                       (define (resume-computation pc)
                         (let/cc k
                           ; When CBOX's contained continuation is called, this set-box!
                           ; will ensure the call returns to right here.
                           (set-box! CBOX k)

                           ; Now, just call the pending computation's continuation
                           ; on the pending computation's interim result!
                           ((pc-continuation pc) (pc-interim-result pc))))

                       ;; run-inference : (listof pc) -> (listof (cons SMC-Value number))
                       ;; Run inference to completion, assuming that the pending-
                       ;; computations have been initialized.
                       (define (run-inference pending-computations)
                         ; Run inference and return the results.
                         ; 1) Resume all the pending computations.
                         ; 2) When they're done (which in parallel require a barrier
                         ;    to ensure we await the resumed computations' completion
                         ;    and some care about what each computation's continuation
                         ;    was), validate that all reached the same breakpoint.
                         ; 3) If all computations completed, return the results.
                         ; 4) Else, (a) resample and (b) recursively continue inference.
                         (local [(define comp-results
                                   (validate-results
                                    (map resume-computation pending-computations)))]
                           (if (not (computation-complete? comp-results))                      
                               (run-inference (resample-all-computations comp-results))
                               ; Done! Return the results: normalized and
                               ; then gathered up into a list of pairs.
                               (collect-results (normalize-pcs comp-results)))))]
                 (run-inference (initialize-all-computations)))]))



;;Helper to make tests a bit shorter
;;Parse and run a program
;;run : sexp -> (listof (cons SMC-Value? number?))
(define (run-program-smc expr)
  (infer-smc (desugar-program (parse-program expr))))




;; Sequential Monte Carlo inference testing! Woot!!!

; These MUST pass. Basic SMC inference with no interesting inference
; involved:
(test (run-program-smc '{infer 1 1}) (list (cons (numV 1) 1)))
(test (run-program-smc '{infer 10 1}) (list (cons (numV 1) 1)))
(test (run-program-smc '{infer 10 "hello"}) (list (cons (stringV "hello") 1)))
(test (run-program-smc '{infer 10 {observe {distribution {list 2 2 3}} = 2}})
      (list (cons (distV (list (numV 2))) 1)))



; These should pass with EXTREMELY high probability because
; the program should fail to pass the "name stack check":
(test/exn (run-program-smc
           '{infer 100 {if {sample {uniform 0 2}}
                           {observe {uniform 0 1} = 0}
                           {observe {uniform 0 1} = 0}}}) "")
(test/exn
 (run-program-smc
  '{infer 100 {with* {{f {fun {} {observe {uniform 0 1} = 0}}}
                      {g {fun {} {f}}}}
                     {if {sample {uniform 0 2}} {f} {g}}}})
 "")


; These tests CAN FAIL but should only do so with low probability.
; They're designed to check that somewhat more substantial inference is working.
(test-inexact-epsilon 0.09)  ; with high probability, we should pass this test!
(define (simple-infer-test)
  (run-program-smc '{infer 500
                           {with* {{die {uniform 0 7}}
                                   {roll1 {sample {uniform 1 7}}}
                                   {roll2 {sample {uniform 1 7}}}
                                   {sum {+ roll1 roll2}}}
                                  {begin {observe {distribution {list {>= sum 6}}} = 1}
                                         roll1}}}))

(define (extract-from-infer-test n results)
  (local [(define pair (assoc (numV n) results))]
    (and pair (exact->inexact (cdr pair)))))
(test (extract-from-infer-test 2 (simple-infer-test))
      (exact->inexact (/ 3 26)))
(test (extract-from-infer-test 3 (simple-infer-test))
      (exact->inexact (/ 4 26)))
(test (extract-from-infer-test 4 (simple-infer-test))
      (exact->inexact (/ 5 26)))
(test (extract-from-infer-test 5 (simple-infer-test))
      (exact->inexact (/ 6 26)))


; Here's a really substantial test. It CAN FAIL but is very unlikely to do so.
; See the comment below for what this program computes.. pretty cool!
(test/pred
 (local [(define
           result
           (run-program-smc
            '{infer
              50
              ; Imagine we have a radar system that is tracking an object in 1 dimension.
              ; We know it started at positions [-4, 4] and with speed [-4, 4].
              ; When it moves, it moves at its speed, plus-or-minus 1.
              ; We get readings from an imprecise sensor giving its actual location.
              ; The sensor gives a distribution of readings around the true value
              ; ranging from 3 below to 3 above (but more likely to be accurate).
              ;
              ; To use probabilistic programming to track the object, we write a program
              ; to GENERATE the sensor readings GIVEN a speed and position (and a series
              ; of movement values, i.e., speed - 1, speed, or speed + 1). Then, we tweak
              ; that program to instead, step-by-step observe that our generated sensor
              ; results MATCH what is observed.
              ;
              ; SMC is perfect for this scenario as most computations will be very poor
              ; choices, but those that are decent choices will be obvious early on.
              ; Eventually, SMC will centre almost all our resources on reasonably probable
              ; computations.
              {rec-with {map {fn xs}
                             {ifelse {empty? xs} empty
                                     {cons {fn {first xs}} {map fn {rest xs}}}}}
                        {with* {{observations {list 3 6 7 14 14 14 19 20}}

                                {speeds {uniform -4 5}}
                                {init-posns {uniform -4 5}}
                     
                                {speed {sample speeds}}
                                {init-posn {sample init-posns}}
                     
                                ; Using binomial coefficients for "spread".
                                ; Could read as up to 3 units in either direction.
                                {sensor-spread
                                 {list -3 -2 -2 -2 -2 -2 -2 -1 -1 -1 -1 -1 -1 -1 -1
                                       -1 -1 -1 -1 -1 -1 -1 0 0 0 0 0 0 0 0 0 0 0 0
                                       0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1
                                       1 2 2 2 2 2 2 3}}
                                {read-sensor
                                 {fun {posn}
                                      {distribution
                                       {map {fun {x} {+ posn x}} sensor-spread}}}}
                     
                                ; When moving, could end up up to 1 unit in either direction.
                                {move-object
                                 {fun {posn}
                                      {with* {{new-posn {+ posn speed}}}
                                             {uniform {- new-posn 1} {+ new-posn 2}}}}}}
                               {rec-with
                                {track-object {curr-posn observed-posns}
                                  {ifelse {empty? observed-posns}
                                          empty
                                          {begin {observe {read-sensor curr-posn}
                                                          = {first observed-posns}}
                                                 {track-object
                                                  {sample {move-object curr-posn}}
                                                  {rest observed-posns}}}}}
                                         {begin
                                           {track-object init-posn observations}
                                           {cons speed init-posn}}}}}}))
         (define top-result (car (last (sort result (lambda (x y) (< (cdr x) (cdr y)))))))]
         top-result)
 (lambda (x)
   ;                   INIT POSN  SPEED
   (or (equal? x (consV (numV 2) (numV 4)))
       (equal? x (consV (numV 3) (numV 3)))
       (equal? x (consV (numV 3) (numV 2)))
       (equal? x (consV (numV 2) (numV 3)))
       (equal? x (consV (numV 3) (numV 4)))
       (equal? x (consV (numV 3) (numV 1))))))
