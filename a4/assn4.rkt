#lang plai

;; CS311 2018W1 A4

(print-only-errors)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DO NOT TOUCH THIS CODE
;; Doing so will make *all our tests fail*
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (get-default-sampler)
  (let ([rng (vector->pseudo-random-generator (vector 1062772744 4224666480 3040273072 1729335656 1332042050 2620454108))])
    (lambda (outcomes)
      (list-ref outcomes (random (length outcomes) rng)))
    ))

(let*
    ([s (get-default-sampler)]
     [l '(1 2 3 4 5 6)]
     [result (list (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l) (s l))])
  (if
   (equal? result '(6 1 1 3 3 5 6 2 2 4 4 4 3 2 4 6))
   "Random generator performing properly. Please do not mess with the generator code, or our tests will fail."
   (error 'get-default-sampler "Your random generator failed the sanity test with result ~v. Please notify the instructors immediately!" result)))


;; ==========================================================
;;                     EBNF & DEFINE-TYPES
;; ==========================================================


;; ISE = Importance Sampling Expression
;;
;; <ISE> ::= <number>
;;     | {distribution <ISE>+}
;;     | {uniform <number> <number>}
;;     | {sample <ISE>}
;;     | {defquery <ISE>}
;;     | {infer <ISE> <ISE>}
;;     | {begin <ISE>+}
;;     | {observe <ISE> <ISE>}
;;     | {<Binop> <ISE> <ISE>}
;;     | {ifelse <ISE> <ISE> <ISE>}
;;     | {with {<id> <ISE>} <ISE>}
;;     | {fun <id> <ISE>}
;;     | {<ISE> <ISE>} ;; function calls, any time the first symbol is not a reserved word
;;     | <id>
;;
;; <Binop> ::= + | - | * | < | > | = | <= | >= | %
;;
;; Note: <id> cannot be one of these reserved words:
;;       with distribution uniform ifelse fun observe begin + - * < > = <= >= %
;;
;; Note: with {uniform a b}, let it be a discrete uniform distribution
;;       from a to b (inclusive). If a > b, then throw an error.

(define-type Binding
  [binding (name symbol?) (named-expr ISE?)])

(define-type ISE
  [distribution (values (listof ISE?))] ;;Distributions must not be empty
  [num (n number?)]
  [id (name symbol?)]
  [binop (op procedure?) (lhs ISE?) (rhs ISE?)]
  [with (b Binding?) (body ISE?)]
  [ifelse (cond ISE?) (t ISE?) (e ISE?)]
  [fun (param symbol?) (body ISE?)]
  [app (function ISE?) (arg ISE?)]
  [sample (distExp ISE?)]
  [defquery (body ISE?)]
  [infer (num-times ISE?) (query ISE?)]
  [rec-begin (expr ISE?) (next ISE?)]
  [observe (dist ISE?) (pred ISE?)])

;; Environments store values, instead of substitutions
(define-type Env
  [mtEnv]
  [anEnv (name symbol?) (value ISE-Value?) (env Env?)])

;; Interpreting a Expression returns a Value
(define-type ISE-Value
  [numV (n number?)]
  [distV (values (and/c (listof ISE-Value?) (not/c empty?)))] ;;Distributions must not be empty
  [rejected] ;; The value that an empty result from observe interprets to
  [thunkV (body ISE?) (env Env?)] ;;A thunk is just closure with no parameter
  ;;Useful for defquery
  [closureV (param symbol?)  ;;Closures wrap an unevaluated function body with its parameter and environment
            (body ISE?)
            (env Env?)])

(define-type ValueXState
  [vals (val ISE-Value?) (state number?)])



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
                     (lambda (num source-count) (make-list (/ source-count elements-gcd) num))
                     elements elements-counts)]
         )
    (sort (flatten new-lists) <))
  )

;;Helper to make tests a bit shorter
;;Parse and run a program, assuming it returns a distV of numV values
;;run : sexp -> ISE-Value?
(define (run pgm)
  (local [(define interpResult (interp (parse pgm)))
          (define result (vals-val interpResult))
          (define state (vals-state interpResult))]
    (if (distV? result)
        (vals (canonical-dist result) state)
        (vals result state))))

;; Helper for testing
;; tests an expression that evaluates to a distV of numV's or a non distV
(define-syntax-rule (test-gen sexp val state)
  (test (local [(define result (run sexp))
                (define v (vals-val result))
                (define s (vals-state result))]
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
              (define v (vals-val result))
              (define s (vals-state result))]
        (if (not (= (length (distV-values v)) (length (distV-values val))))
            (show-failed-test (cons v s))
            (let* ([cv (distV (map (lambda (d)
                                     (if (distV? d) (canonical-dist d) d))
                                   (distV-values v)))]
                   [result (and (compare-nested-dist (distV-values cv) (distV-values val))
                                (= state s))])
              (if result
                  (test #t #t)
                  (show-failed-test (cons v s)))))))))


;; ==========================================================
;;                           PARSE
;; ==========================================================

;; lookup-op : symbol -> (or procedure false)
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
    ['% modulo]
    [_ #f]))

;; op-exists? : symbol -> boolean
(define (op-exists? op) (if (lookup-op op) #t #f))
(test (op-exists? '*) #t)
(test (op-exists? 'with) #f)


;; reserved? : symbol -> boolean
(define (reserved? word)
  (if (or
       (member word '(with distribution uniform sample defquery infer ifelse observe begin))
       (lookup-op word))
      #t
      #f))
(test (reserved? '*) #t)
(test (reserved? 'with) #t)
(test (reserved? 'foo) #f)

;; parse : s-exp -> ISE
;; Consumes an s-expression and generates the corresponding ISE
(define (parse sexp)
  (local [(define valid-id? (lambda (id)
                              (and (symbol? id)
                                   (not (or (op-exists? id) (reserved? id))))))]
    (match sexp
      [(? number?)
       (num sexp)]
      [(list (and op (? symbol?) (? op-exists?)) lhs rhs)
       (binop (lookup-op op) (parse lhs) (parse rhs))]
      [(list 'ifelse condn then elsee)
       (ifelse (parse condn) (parse then) (parse elsee))]
      [(list 'with (list (and (? valid-id?) id) value) body) (with (binding id (parse value)) (parse body))]
      [(list 'uniform (? number? a) (? number? b))
       (if (< a b)
           (distribution (map num (range a b)))
           (error "Cannot create empty distribution") )]
      [(cons 'distribution values)
       (if (empty? values)
           (error "Cannot create empty distribution")
           (distribution (map parse values)))]
      [(list 'infer numruns query)
       (infer (parse numruns) (parse query))]
      [(list 'defquery query)
       (defquery (parse query))]
      [(list 'sample expr)
       (sample (parse expr))]
      [(and (? symbol?) (not (? reserved?)))
       (id sexp)]
      [(list 'observe dist pred)
       (observe (parse dist) (parse pred))]
      [(list 'begin expr)
       (parse expr)]
      [(list 'begin expr next ...)
       (rec-begin (parse expr) (parse (cons 'begin next)))]
      [(cons (and word (? reserved?)) _)
       (error 'parse "Misused reserved word ~a in: ~a" word sexp)]
      [(list 'fun (? valid-id? param) body) (fun param (parse body))]
      [(list f arg) (app (parse f) (parse arg))]
      [_
       (error 'parse "Unable to recognize expr: ~a" sexp)]
      )))

(define (num-lt x y)
  (< (num-n x) (num-n y)))



;; ==========================================================
;;                           INTERP
;; ==========================================================

;;wrapResult : (or boolean? number?) -> ISE?
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


;; interp : ISE -> ValueXState
;; This procedure interprets the given ISE and produces a result
;; in the form of a ISE-Value (either a closureV, thunkV, or numV)
;; and a weight (a number representing the probability)
;; using a specifically seeded random number
(define (interp expr)
  (local [(define lookup
            ;; lookup looks up a variable name in a env
            (lambda (id env)
              (type-case Env env
                [mtEnv () (error "free variable")]
                [anEnv (name value anotherEnv) (if (symbol=? id name)
                                                   value
                                                   (lookup id anotherEnv))])))
          (define sample-from-dist (get-default-sampler))

          ;; ISE Env number -> ValueXState
          ;; helper for interp
          (define interp-helper
            (lambda (expr env state)
              (type-case ISE expr
                [id (name) (vals (lookup name env) state)]
                [num (n) (vals (numV n) state)]
                [binop (op lhs rhs)
                       (local [(define result (interp-helper lhs env state))
                               (define lhsV (vals-val result))
                               (define S1 (vals-state result))]
                         (type-case ISE-Value lhsV
                           [numV (n1)
                                 (local [(define result (interp-helper rhs env S1))
                                         (define rhsV (vals-val result))
                                         (define S2 (vals-state result))]
                                   (type-case ISE-Value rhsV
                                     [numV (n2) (vals (wrapResult (op n1 n2)) S2)]
                                     [rejected () (vals (rejected) 0)]
                                     [else (error "non-numerical value in binop rhs")]))]
                           [rejected () (vals (rejected) 0)]
                           [else (error "non-numerical value in binop lhs")]))]
                [ifelse (cond conseq altern)
                        (local [(define result (interp-helper cond env state))
                                (define condV (vals-val result))
                                (define S1 (vals-state result))]
                          (type-case ISE-Value condV
                            [numV (n) (if (not (= n 0))
                                          (interp-helper conseq env S1)
                                          (interp-helper altern env state))]
                            [rejected () (vals (rejected) 0)]
                            [else (error "non-boolean value in ifelse test")]))]
                [fun (param body) (vals (closureV param body env) state)]
                [app (f arg)
                     (local [(define first (interp-helper f env state))
                             (define fV (vals-val first))
                             (define S1 (vals-state first))
                             (define second (interp-helper arg env state))
                             (define argV (vals-val second))
                             (define S2 (vals-state second))]
                       (cond [(or (rejected? fV) (rejected? argV)) (vals (rejected) 0)]
                             [(not (closureV? fV)) (error 'app "Function has to be a closureV!")]
                             [else
                              (let* ([param  (closureV-param fV)]
                                     [body   (closureV-body fV)]
                                     [cEnv   (closureV-env fV)]
                                     [newEnv (anEnv param argV cEnv)])
                                (interp-helper body newEnv S1))]))]
                [with (bnd body)
                      (interp-helper (app (fun (binding-name bnd) body)
                                          (binding-named-expr bnd))
                                     env
                                     state)]
                [distribution (elems)
                              (local [;; ISE Env number -> (vals (listof ISE-Value) number)
                                      ;; Evaluates a list of ISE's to a list of ISE-Value's and resulting state
                                      (define (interp-list exprs env state)
                                        (if (empty? exprs)
                                            (values empty state)
                                            (local [(define firstResult (interp-helper (first exprs) env state))
                                                    (define expr-val (vals-val firstResult))
                                                    (define expr-state (vals-state firstResult))
                                                    (define-values (rest-vals rest-state) (interp-list (rest exprs) env expr-state))]
                                              (values (cons expr-val rest-vals) rest-state))))
                                      (define-values (elemsV S1) (interp-list elems env state))]
                                (if (or (empty? elemsV) (member (rejected) elemsV))
                                    (vals (rejected) 0)
                                    (vals (distV elemsV) S1)))]
                [sample (e)
                        (local [(define result (interp-helper e env state))
                                (define v (vals-val result))
                                (define S1 (vals-state result))]
                          (type-case ISE-Value v
                            [rejected () (vals (rejected) 0)]
                            [distV (listVals)
                                   (if (empty? listVals)
                                       (error "Cannot sample empty distribution")
                                       (vals (sample-from-dist listVals) S1))]
                            [else (error "Can only sample distributions")]))]
                [defquery (body) (vals (thunkV body env) state)]
                [infer (n query)
                       (local [(define n-result (interp-helper n env state))
                               (define n-val (vals-val n-result))
                               (define n-state (vals-state n-result))
                               (define q-result (interp-helper query env n-state))
                               (define q-val (vals-val q-result))
                               (define q-state (vals-state q-result))]
                         (type-case ISE-Value n-val
                           [numV (num)
                                 (type-case ISE-Value q-val
                                   [thunkV (body thunk-env)
                                           (local [(define (rec-exec-query count executable-query relay-env acc)
                                                     (cond [(zero? count) acc]
                                                           [else
                                                            (rec-exec-query (sub1 count)
                                                                            executable-query
                                                                            relay-env
                                                                            (append acc
                                                                                    (local [(define result (interp-helper executable-query relay-env 1))
                                                                                            (define res-val (vals-val result))
                                                                                            (define res-state (vals-state result))]
                                                                                      (if (rejected? res-val)
                                                                                          '()
                                                                                          (list res-val)))))]))
                                                   (define query-result (rec-exec-query num body thunk-env '()))]
                                             (if (not (empty? query-result))
                                                 (vals (distV query-result) q-state)
                                                 (error "Filtered list should not be empty.")))]
                                   [rejected () (vals (rejected) 0)]
                                   [else (error "Expected query to be of type thunkV.")])]
                           [rejected () (vals (rejected) 0)]
                           [else (error "Expected a number as the first parameter.")]))]
                [rec-begin (expr next)  
                           (local [(define e-result (interp-helper expr env state))
                                   (define S1 (vals-state e-result))]
                             (if (rejected? e-result)
                                 (vals (rejected) 0)
                                 (interp-helper next env S1)))]
                [observe (dist pred)
                         (local [(define d-result (interp-helper dist env state))
                                 (define d-val (vals-val d-result))
                                 (define d-state (vals-state d-result))]
                           (type-case ISE-Value d-val
                             [distV (values)
                                    (if (empty? values)
                                        (vals (rejected) 0)
                                        (local [(define isV-true?
                                                  (compose not zero? numV-n))
                                                (define (pred-runner val)
                                                  (local [(define pred-result
                                                            (interp-helper (app pred (num (numV-n val))) env d-state))]
                                                    (vals-val pred-result)))
                                                (define new-list
                                                  (filter (compose isV-true? pred-runner) values))
                                                (define new-state    
                                                  (* d-state (/ (length new-list) (length values))))]
                                          (if (empty? new-list)
                                              (vals (rejected) 0)
                                              (vals (distV new-list) new-state))))]
                             [rejected () (vals (rejected) 0)]
                             [else (error 'interp "Expected a distV.")]))])))]
    ;; start with an empty env and weight of 1
    (interp-helper expr (mtEnv) 1)))



;; ==========================================================
;;                         A5 TESTS
;; ==========================================================
;; NOTE: TO MAKE SURE THE TEST SUITES DON'T TAKE TOO MUCH TIME
;;       TO RUN, MOST OF THE TESTS DON'T INFER MANY TIMES
;;       (MOST OF THEM LESS THAN 50), BUT TO ACCURATELY
;;       APPROXIMATE PROBABILITY, WE NORMALLY NEED TO INFER
;;       MUCH MORE TIMES (E.G. 1000)


;; Tests for parse
(test (parse '{begin {distribution 1 2 3}
                     {defquery 1}
                     {fun x x}})
      (rec-begin (distribution (list (num 1) (num 2) (num 3))) (rec-begin (defquery (num 1)) (fun 'x (id 'x)))))

(test (parse '{begin {distribution 1 2 3}
                     {distribution 1 2 3}
                     {distribution 1 2 3}
                     {distribution 1 2 3}})
      (rec-begin (distribution (list (num 1) (num 2) (num 3)))
                 (rec-begin (distribution (list (num 1) (num 2) (num 3)))
                            (rec-begin (distribution (list (num 1) (num 2) (num 3))) (distribution (list (num 1) (num 2) (num 3)))))))

(test (parse '{with {d {distribution 4 5 6}}
                    {begin 1 d 2}})
      (with (binding 'd (distribution (list (num 4) (num 5) (num 6))))
            (rec-begin (num 1) (rec-begin (id 'd) (num 2)))))

(test/exn (parse '{begin}) "")
    
;; the result of throwing a coin 10 times
(test-gen
 '{infer 10 {defquery {sample {uniform 0 2}}}}
 (distV (map numV '(0 0 0 1 1)))
 1)

;; Infer the probability of rolling a die and getting a number > 2
; approach 1
(test-gen
 '{with {d {uniform 1 7}}
        {observe
         {infer 10 {defquery {sample d}}}
         {fun x {> x 2}}}}
 (distV (map numV '(3 3 4 5 6 6)))
 (/ 3 5))

; approach 2
(test-gen
 '{with {q {defquery
             {with {result {sample {uniform 1 7}}}
                   {ifelse {> result 2} 1 0}}}}
        {infer 10 q}}
 (distV (map numV '(0 0 1 1 1)))
 1)

;; Infer the probability of rolling a die and getting
;;  a number > 2 and < 5

; approach 1
(test-gen
 '{with {d {uniform 1 6}}
        {observe {observe {infer 10 {defquery {sample d}}}
                          {fun x {> x 2}}}
                 {fun x {< x 5}}}}
 (distV (map numV '(3 3 4)))
 (/ 3 10))

; approach 2
(test-gen
 '{with {q {defquery
             {with {result {sample {uniform 1 6}}}
                   {ifelse {> result 2}
                           {ifelse {< result 5} 1 0}
                           0}}}}
        {infer 10 q}}
 (distV (map numV '(0 0 0 0 0 0 0 1 1 1)))
 1)

;; Infer the distribution of results of sampling from a distribution
;;  and yielding a number less than 5
(test-nested
 '{infer 3 {defquery
             {observe {infer 3 {defquery {sample {distribution 1 1 2 3 4 4 4 5 6 8 8}}}}
                      {fun x {< x 5}}}}}
 (distV (list (distV (list (numV 4)))
              (distV (list (numV 1)))
              (distV (map numV '(1 2)))))
 1)

;; Sampling from uniform distribution 20 times should have 1/2 chance
;;  of yielding exactly half of the distribution
(test-gen
 '{observe
   {infer 20 {defquery {sample {uniform 1 5}}}}
   {fun x {< x 3}}}
 (distV (map numV '(1 1 1 2 2)))
 (/ 1 2))

;; Rolling 2 dice should have the chance of 5/36 (~ 0.13)
;;  of getting a sum of 6
(test-gen
 '{with {d {uniform 1 7}}
        {with {result {infer 100 {defquery
                                   {with {x {sample d}}
                                         {with {y {sample d}}
                                               {+ x y}}}}}}
              {begin
                {observe result {fun x {= x 6}}}
                result}}}
 (distV (map numV '(2 2 2 2
                      3 3 3 3
                      4 4 4 4 4 4 4 4 4 4 4 4 4
                      5 5 5 5 5 5 5 5 5
                      6 6 6 6 6 6 6 6 6 6 6 6 6
                      7 7 7 7 7 7 7 7 7 7 7
                      8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8 8
                      9 9 9 9 9 9 9 9 9 9 9 9 9
                      10 10 10 10 10 10 10 10 10 10
                      11 11 11 11
                      12)))
 (/ 13 100))

;; Compute the probability of yielding a sum of 4
;;  by adding 2 numbers sampled from 2 distributions,
;;  returning the list of sums
(test-gen
 '{with {d1 {distribution 1 1 1 2 2}}
        {with {d2 {distribution 3 4 4}}
              {with {result
                     {infer 10 {defquery {+ {sample d1} {sample d2}}}}}
                    {begin
                      {observe result {fun x {= x 4}}}
                      result}}}}
 (distV (map numV '(4 4 5 5 5 5 5 5 5 6)))
 (/ 1 5))

;; Roll a fair die and then a biased die, what's the chance of rolling a number < 2 both times?

; approach 1
(test-gen
 '{with {fair {uniform 1 7}}
        {with {biased {distribution 1 1 2 2 2 3 4 5 6}}
              {with {f {fun x {< x 2}}}
                    {begin
                      {with {result {infer 1000 {defquery {sample fair}}}}
                            {observe result f}}
                      {with {result {infer 1000 {defquery {sample biased}}}}
                            {observe result f}}}}}}
 (distV (list (numV 1)))
 (/ 7821 200000))

; approach 2
(test-gen
 '{with {q {defquery
             {with {fair {sample {uniform 1 7}}}
                   {with {biased {sample {distribution 1 1 2 2 2 3 4 5 6}}}
                         {ifelse {< fair 2}
                                 {ifelse {< biased 2}
                                         1
                                         0}
                                 0}}}}}
        {infer 1000 q}}
 (distV (map numV '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                      0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1)))
 1)

;; After a coin toss, you have a 2/3 chance of drawing a fair die if heads,
;;  otherwise you have a 2/3 chance of drawing a biased die. Infer the probability
;;  that rolling the die would result in a number >= 4?
(test-gen
 '{with {coin {distribution 0 1}}
        {with {fair {uniform 1 7}}
              {with {biased {distribution 1 1 2 2 2 3 4 5 6}}
                    {with {result {infer 50
                                         {defquery
                                           {ifelse {= 0 {sample coin}}
                                                   {with {die {sample {distribution fair fair biased}}}
                                                         {sample die}}
                                                   {with {die {sample {distribution fair biased biased}}}
                                                         {sample die}}}}}}
                          {observe result {fun x {> x 3}}}}}}}
 (distV (map numV '(4 4 5 5 5 5 6 6 6)))
 (/ 9 25))
       
;; The probability of returning a number not in a distribution
;;  is zero
(test-gen
 '{observe {infer 10
                  {defquery {sample {uniform 2 11}}}}
           {fun x {< x 1}}}
 (rejected)
 0)

;; Each element in ditribution should be evaluated, with state conserved
(test-gen
 '{distribution 1 2 3
                {sample {observe {uniform 0 2}
                                 {fun x {< x 1}}}}
                4 5 6}
 (distV (map numV '(0 1 2 3 4 5 6)))
 (/ 1 2))

;; Infer should return the original state independent of defquery execution
(test-nested
 '{begin
    {observe {uniform 1 3} {fun x {< x 2}}}
    {infer 5
           (defquery {with {d {distribution 1 2 3 4 5 6}}
                           {observe d {fun x {> x 2}}}})}}
 (distV (list (distV (map numV '(3 4 5 6)))
              (distV (map numV '(3 4 5 6)))
              (distV (map numV '(3 4 5 6)))
              (distV (map numV '(3 4 5 6)))
              (distV (map numV '(3 4 5 6)))))
 (/ 1 2))

;; observe should ignore state changes in function
(test-gen
 '{with {d {distribution 2 3}}
        {with {f {fun x {begin
                          {observe {distribution 1 2 3}
                                   {fun y {< y 2}}}
                          {< x 3}}}}
              {observe d f}}}
 (distV (list (numV 2)))
 (/ 1 2))


;; Rejected should be propagated
(test-gen
 '{sample {observe {uniform 1 6}
                   {fun x {> x 6}}}}
 (rejected)
 0)

(test-gen
 '{with {f {fun x x}}
        {f {observe {uniform 0 1} {fun x {> x 1}}}}}
 (rejected)
 0)

(test-gen
 '{observe {observe {uniform 0 1} {fun x x}} {fun x 1}}
 (rejected)
 0)


;; Error cases
(test/exn
 (run '{infer 10 
              {defquery {observe {uniform 0 1}
                                 {fun x {> x 1}}}}})
 "")

(test/exn
 (run '{observe {sample {distribution 1 2}} {fun x x}})
 "")

(test/exn
 (run '{observe {uniform 1 3} 1})
 "")

(test/exn
 (run '{{defquery 1} 1})
 "")

(test/exn
 (run '{infer {uniform 1}
              {defquery 1}})
 "")

(test/exn
 (run '{infer 10
              {fun x x}})
 "")
