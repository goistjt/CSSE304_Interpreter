;:  Single-file version of the interpreter.
;; Easier to submit to server
(define eval-count 1)
(define p "")

(define indent-level 0)
(define display-traced-output
	(case-lambda
		[(level name args)
			(let loop ([level level])
				(if (zero? level)
					(begin
						(display (cons name args)) (newline))
					(begin
						(display "| ")
						(loop (sub1 level)))))]
		[(level result)
			(let loop ([level level])
				(if (zero? level)
					(begin 
						(display result) (newline))
					(begin
						(display "| ")
						(loop (sub1 level)))))]))

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

(define list-of
	(lambda (pred)
		(lambda (val)
			(or (null? val)
				(and (pair? val)
					 (pred (car val))
					 ((list-of pred) (cdr val)))))))
					 
(define literal?
	(lambda (arg)
		(or (number? arg) (char? arg) (string? arg) (boolean? arg) (vector? arg) (list? arg) (symbol? arg) (pair? arg))))
(define bindings?
	(lambda (arg)
		(or (null? arg) (symbol? arg) ((list-of symbol?) arg) 
			(and (symbol? (car arg)) (bindings? (cdr arg))))))

(define-datatype expression expression?
	[lit-exp (id literal?)]
	[var-exp (id symbol?)]
	[if-exp
		(condition expression?)
		(true expression?)]
	[if-else-exp
		(condition expression?)
		(true expression?)
		(false expression?)]
	[lambda-exp
		(vars bindings?)
		(bodies (list-of expression?))]
	[ref-lambda-exp
		(vars (list-of literal?))
		(bodies (list-of expression?))]
	[let-exp
		(bound bindings?)
		(bound-to (list-of expression?))
		(bodies (list-of expression?))]
	[let*-exp
		(bound bindings?)
		(bound-to (list-of expression?))
		(bodies (list-of expression?))]
	[named-let-exp
		(name symbol?)
		(bound bindings?)
		(bound-to (list-of expression?))
		(bodies (list-of expression?))]
	[letrec-exp
		(names (list-of symbol?))
		(bound-to (list-of expression?))
		(bodies (list-of expression?))]
	[set!-exp
		(variable symbol?)
		(new-value expression?)]
	[when-exp
		(test expression?)
		(bodies (list-of expression?))]
	[cond-exp 
		(tests (list-of expression?))
		(results (list-of (list-of expression?)))]
	[begin-exp 
		(bodies (list-of expression?))]
	[and-exp 
		(bodies (list-of expression?))]
	[or-exp 
		(bodies (list-of expression?))]
	[while-exp 
		(condition expression?)
		(bodies (list-of expression?))]
	[for-loop-exp
		(init expression?)
		(test expression?)
		(update expression?)
		(bodies (list-of expression?))]
	[case-exp 
		(value expression?)
		(cases (list-of literal?))
		(results (list-of (list-of expression?)))]
	[trace-lambda-exp
		(trace-name symbol?)
		(vars bindings?)
		(bodies (list-of expression?))]
	[case-lambda-exp
		(vars-cases (list-of (list-of symbol?)))
		(body-cases (list-of (list-of expression?)))]
	[define-exp
		(name symbol?)
		(value expression?)]
	[app-exp
		(exprs (list-of expression?))])

;; environment type definitions

(define scheme-value?
 	(lambda (x) #t))

(define-datatype environment environment?
 	[empty-env-record]
 	[extended-env-record
 	 	(syms (list-of symbol?))
 	 	(vals (list-of scheme-value?))
 	 	(env environment?)]
 	[recursively-extended-env-record
 		(names (list-of symbol?))
 		(vals (list-of scheme-value?))
 		(env environment?)])

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
	[prim-proc
		(name symbol?)]
	[prop-closure
		(vars bindings?)
		(bodies (list-of expression?))
		(env environment?)]
	[imp-closure
		(vars bindings?)
		(bodies (list-of expression?))
		(env environment?)]
	[sym-closure
		(vars bindings?)
		(bodies (list-of expression?))
		(env environment?)]
	[ref-closure
		(vars (list-of literal?))
		(bodies (list-of expression?))
		(env environment?)]
	[case-closure
		(vars-cases (list-of (list-of symbol?)))
		(body-cases (list-of (list-of expression?)))
		(env environment?)]
	[trace-prop-closure
		(trace-name symbol?)
		(vars bindings?)
		(bodies (list-of expression?))
		(env environment?)]
	[trace-imp-closure
		(trace-name symbol?)
		(vars bindings?)
		(bodies (list-of expression?))
		(env environment?)]
	[trace-sym-closure
		(trace-name symbol?)
		(vars bindings?)
		(bodies (list-of expression?))
		(env environment?)])
	 
;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+

(define parse-exp 
	(lambda (datum)
		(cond 
			[(symbol? datum) (var-exp datum)]
			[(or (number? datum) (string? datum) (char? datum) (boolean? datum) (vector? datum))
				(lit-exp datum)]
			[(not (list? datum)) 
				(eopl:error 'parse-exp "expression must be a proper list: ~s" 
							datum)]
			[(eq? (car datum) 'quote) (lit-exp (cadr datum))]
			[(eq? (car datum) 'lambda)
				(cond
					[(or (null? (cdr datum)) (null? (cddr datum)))
						(eopl:error 'parse-exp "Incomplete lambda expression: ~s" datum)]
					[(not (bindings? (cadr datum)))
						(if (let ref-check ([vars (cadr datum)])
								(cond 
									[(null? vars) #f]
									[(and (list? (car vars)) (eq? (caar vars) 'ref)) #t]
									[else (ref-check (cdr vars))]))
							(ref-lambda-exp (cadr datum) (map parse-exp (cddr datum)))
							(eopl:error 'parse-exp "Bound variables must be symbols: ~s" datum))]
					[else (lambda-exp (cadr datum) (map parse-exp (cddr datum)))])]
			[(eq? (car datum) 'if)
				(cond
					[(null? (cdr datum)) 
						(eopl:error 'parse-exp "If missing test & cases: ~s" datum)]
					[(null? (cddr datum))
						(eopl:error 'parse-exp "If missing cases: ~s" datum)]
					[(null? (cdddr datum))
						(if-exp (parse-exp (cadr datum)) (parse-exp (caddr datum)))]
					[(null? (cddddr datum))
						(if-else-exp (parse-exp (cadr datum)) 
							(parse-exp (caddr datum)) (parse-exp (cadddr datum)))]
					[else (eopl:error 'parse-exp "If has too many arguments: ~s" datum)])]
			[(eq? (car datum) 'let)
				(cond
					[(symbol? (cadr datum))
						(cond
						    [(or (null? (cddr datum)) (null? (cdddr datum)))
						        (eopl:error 'parse-exp "Named let missing elements: ~s" 
									datum)]
							[(not (list? (caddr datum)))
								(eopl:error 'parse-exp "Named let bindings must be a proper list: ~s" 
									datum)]
							[(not ((list-of list?) (caddr datum)))
								(eopl:error 'parse-exp "Not all named let bindings are proper lists: ~s" 
									datum)]
							[(not ((list-of symbol?) (map car (caddr datum))))
								(eopl:error 'parse-exp "Not all let bound variables are symbols: ~s" 
									datum)]
							[(ormap null? (map cdr (caddr datum))) ; This is checking for length 1
								(eopl:error 'parse-exp "Named let bindings must be of length 2: ~s" 
									datum)]
							[(not ((list-of null?) (map cddr (caddr datum))))
							    (eopl:error 'parse-exp "Named let bindings must be of length 2: ~s" 
									datum)]
							[else (named-let-exp (cadr datum) (map car (caddr datum)) 
                                (map parse-exp (map cadr (caddr datum))) (map parse-exp (cdddr datum)))])]
					[else
						(cond
						   [(or (null? (cdr datum)) (null? (cddr datum)))
						        (eopl:error 'parse-exp "Let missing elements: ~s" 
									datum)]
							[(not (list? (cadr datum)))
								(eopl:error 'parse-exp "Let bindings must be a proper list: ~s" 
									datum)]
							[(not ((list-of list?) (cadr datum)))
								(eopl:error 'parse-exp "Not all let bindings are proper lists: ~s" 
									datum)]
							[(not ((list-of symbol?) (map car (cadr datum))))
								(eopl:error 'parse-exp "Not all let bound variables are symbols: ~s" 
									datum)]
							[(ormap null? (map cdr (cadr datum))) ; This is checking for length 1
								(eopl:error 'parse-exp "Let bindings must be of length 2: ~s" 
									datum)]
							[(not ((list-of null?) (map cddr (cadr datum))))
							    (eopl:error 'parse-exp "Let bindings must be of length 2: ~s" 
									datum)]
							[else (let-exp (map car (cadr datum)) (map parse-exp 
                            	(map cadr (cadr datum))) (map parse-exp (cddr datum)))])])]
            [(eq? (car datum) 'let*)
             	(cond
                 	[(or (null? (cdr datum)) (null? (cddr datum)))
						(eopl:error 'parse-exp "Let* missing elements: ~s" 
							datum)]
					[(not (list? (cadr datum)))
						(eopl:error 'parse-exp "Let* bindings must be a proper list: ~s" 
							datum)]
					[(not ((list-of list?) (cadr datum)))
						(eopl:error 'parse-exp "Not all let* bindings are proper lists: ~s" 
							datum)]
					[(not ((list-of symbol?) (map car (cadr datum))))
						(eopl:error 'parse-exp "Not all let* bound variables are symbols: ~s" 
							datum)]
					[(ormap null? (map cdr (cadr datum))) ; This is checking for length 1
								(eopl:error 'parse-exp "Let* bindings must be of length 2: ~s" 
									datum)]
					[(not ((list-of null?) (map cddr (cadr datum))))
						(eopl:error 'parse-exp "Let* bindings must be of length 2: ~s" 
							datum)]
					[else (let*-exp (map car (cadr datum)) (map parse-exp 
                    	(map cadr (cadr datum))) (map parse-exp (cddr datum)))])]
            [(eq? (car datum) 'letrec)
             	(cond
                 	[(or (null? (cdr datum)) (null? (cddr datum)))
                     	(eopl:error 'parse-exp "Letrec missing elements: ~s" 
							datum)]
                 	[(not (list? (cadr datum)))
                     	(eopl:error 'parse-exp "Letrec bindings must be a proper list: ~s" 
							datum)]
                 	[(not ((list-of symbol?) (map car (cadr datum))))
                     	(eopl:error 'parse-exp "Letrec bound variables must symbols: ~s" 
							datum)]
                 	[(or (ormap null? (map cdr (cadr datum))) 
						(not ((list-of null?) (map cddr (cadr datum)))))
                     	(eopl:error 'parse-exp "Letrec bindings must be of length 2: ~s" 
							datum)]
                 	[(not ((list-of list?) (cadr datum)))
                     	(eopl:error 'parse-exp "Not all letrec bindings are proper lists: ~s" 
							datum)]
                 	[else (letrec-exp (map car (cadr datum)) (map parse-exp 
                    	(map cadr (cadr datum))) (map parse-exp (cddr datum)))])]
			[(eq? (car datum) 'set!)
             	(cond
                	[(or (null? (cdr datum)) (null? (cddr datum)))
                    	(eopl:error 'parse-exp "set! missing elements: ~s" 
							datum)]
                 	[(not (symbol? (cadr datum)))
                     	(eopl:error 'parse-exp "set! variable must be a symbol: ~s" 
							datum)]
                 	[(not (null? (cdddr datum)))
                     	(eopl:error 'parse-exp "set! only takes 2 arguments: ~s" 
							datum)]
                 	[else (set!-exp (cadr datum) (parse-exp (caddr datum)))])]
            [(eq? (car datum) 'when)
             	(cond 
             		[(or (null? (cdr datum)) (null? (cddr datum)))
             			(eopl:error 'parse-exp "when must have at least two arguments: ~s"
             				datum)]
             		[else (when-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))])]
			[(eq? (car datum) 'cond)
				(cond 
					[(null? (cdr datum))
             			(eopl:error 'parse-exp "cond must have at least one condition: ~s"
             				datum)]
             		[(ormap null? (map cdr (cdr datum)))
             			(eopl:error 'parse-exp "cond conditionals must have at least one body: ~s"
             				datum)]
             		[else (cond-exp (map parse-exp (map car (cdr datum)))
             			(map (lambda (ls) (map parse-exp ls)) (map cdr (cdr datum))))])]
			[(eq? (car datum) 'begin)
				(cond 
					[(null? (cdr datum))
						(eopl:error 'parse-exp
							"Begin requires at least 1 argument: ~s" datum)]
					[else (begin-exp (map parse-exp (cdr datum)))])]
			[(eq? (car datum) 'and)
				(and-exp (map parse-exp (cdr datum)))]
			[(eq? (car datum) 'or)
				(or-exp (map parse-exp (cdr datum)))]
			[(eq? (car datum) 'while)
				(cond 
					[(or (null? (cdr datum)) (null? (cddr datum)))
             			(eopl:error 'parse-exp "while must have a condition and at least one body: ~s"
             				datum)]
             		[else (while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))])]
			[(eq? (car datum) 'for-loop)
				(cond 
					[(or (null? (cdr datum)) (null? (cddr datum)))
             			(eopl:error 'parse-exp "for must have a test and at least one body: ~s"
             				datum)]
             		[(or (null? (cdadr datum)) (null? (cddadr datum)))
             			(eopl:error 'parse-exp "for must have init, test, and update expressions: ~s"
             				datum)]
             		[else (for-loop-exp (parse-exp (caadr datum)) (parse-exp (cadadr datum))
             			(parse-exp (car (cddadr datum))) (map parse-exp (cddr datum)))])]
			[(eq? (car datum) 'case)
				(cond 
					[(null? (cdr datum))
             			(eopl:error 'parse-exp "case must have at least one condition: ~s"
             				datum)]
             		[(ormap null? (map cdr (cdr datum)))
             			(eopl:error 'parse-exp "case conditionals must have at least one body: ~s"
             				datum)]
             		[else (case-exp (parse-exp (cadr datum)) 
             			(map car (cddr datum))
             			(map (lambda (ls) (map parse-exp ls)) (map cdr (cddr datum))))])]
			[(eq? (car datum) 'trace-lambda)
				(cond
					[(or (null? (cdr datum)) (null? (cddr datum)) (null? (cdddr datum)))
						(eopl:error 'parse-exp "Incomplete trace-lambda expression: ~s" datum)]
					[(not (symbol? (cadr datum)))
						(eopl:error 'parse-exp "name must be a symbol: ~s" datum)]
					[(not (bindings? (caddr datum))) 
						(eopl:error 'parse-exp "Bound variables must be symbols: ~s" datum)]
					[else (trace-lambda-exp (cadr datum) (caddr datum) 
						(map parse-exp (cdddr datum)))])]
			[(eq? (car datum) 'case-lambda)
				(cond 
					[(null? (cdr datum))
						(eopl:error 'parse-exp "Incomplete case-lambda expression: ~s" datum)]
					[(ormap (lambda (x) (not ((list-of symbol?) x))) (map car (cdr datum)))
						(eopl:error 'parse-exp "case-lambda cases must be lists of symbols: ~s" datum)]
					[(ormap null? (map cdr (cdr datum)))
						(eopl:error 'parse-exp "case-lambda must have right halves: ~s" datum)]
					[else (case-lambda-exp
							(map car (cdr datum))
							(map (lambda (ls) (map parse-exp ls)) (map cdr (cdr datum))))])]
			[(eq? (car datum) 'define)
				(cond 
					[(or (null? (cdr datum)) (null? (cddr datum)) (not (null? (cdddr datum))))
						(eopl:error 'parse-exp "incorrect number of args to define: ~s" datum)]
					[(not (symbol? (cadr datum)))
						(eopl:error 'parse-exp "Define name must be a symbol: ~s" datum)]
					[else (define-exp (cadr datum) (parse-exp (caddr datum)))])]
			[else (app-exp (map parse-exp datum))])))

(define unparse-exp
  	(lambda (expr)
      	(cases expression expr
            [var-exp (id) id]
            [lit-exp (id) id]
            [if-exp (condition true)
                (list 'if (unparse-exp condition) (unparse-exp true))]
            [if-else-exp (condition true false)
                (list 'if (unparse-exp condition) 
					(unparse-exp true) (unparse-exp false))]
            [lambda-exp (vars bodies)
                (cons 'lambda (cons vars (map unparse-exp bodies)))]
            [ref-lambda-exp (vars bodies)
            	(cons 'lambda (cons vars (map unparse-exp bodies)))]
            [let-exp (bound bound-to bodies)
                (cons 'let (cons (make-pairs bound 
					(map unparse-exp bound-to)) (map unparse-exp bodies)))]
            [let*-exp (bound bound-to bodies)
                (cons 'let* (cons (make-pairs bound 
					(map unparse-exp bound-to)) (map unparse-exp bodies)))]
            [named-let-exp (name bound bound-to bodies)
                (cons 'let (cons name (cons (make-pairs bound 
					(map unparse-exp bound-to)) (map unparse-exp bodies))))]
            [letrec-exp (names bound-to bodies)
                (cons 'letrec (cons (make-pairs names 
					(map unparse-exp bound-to)) (map unparse-exp bodies)))]
            [set!-exp (variable new-value)
                (list 'set! variable (unparse-exp new-value))]
            [when-exp (test bodies)
              	(cons 'when (cons (unparse-exp test) (map unparse-exp bodies)))]
            [cond-exp (tests bodies)
              	(cons 'cond 
              		(map (lambda (ls1 ls2) (cons (unparse-exp ls1) ls2)) 
               			tests (map (lambda (x) (map unparse-exp x)) bodies)))]
            [begin-exp (bodies) 
            	(cons 'begin (map unparse-exp bodies))]
            [and-exp (bodies)
            	(cons 'and (map unparse-exp bodies))]
            [or-exp (bodies)
            	(cons 'or (map unparse-exp bodies))]
            [while-exp (condition bodies)
            	(cons 'while (cons (unparse-exp condition) (map unparse-exp bodies)))]
            [for-loop-exp (init test update bodies)
            	(cons 'for (cons (list (unparse-exp init) (unparse-exp test) (unparse-exp update))
            		(map unparse-exp bodies)))]
            [case-exp (test cases bodies)
            	(cons 'case (cons (unparse-exp test) 
            		(map (lambda (ls1 ls2) (cons ls1 ls2))
            			cases (map (lambda (x) (map unparse-exp x)) bodies))))]
            [trace-lambda-exp (name vars bodies)
            	(cons 'trace-lambda (cons name (cons vars (map unparse-exp bodies))))]
            [case-lambda-exp (vars-cases body-cases)
            	(cons 'case-lambda (make-pairs vars-cases 
            						(map (lambda (ls) (map unparse-exp ls)) body-cases)))]
            [define-exp (name value)
            	(list 'define name (unparse-exp value))]
            [app-exp (exprs) (map unparse-exp exprs)])))
                             
(define make-pairs
	(lambda (var expr)
    	(if (null? var)
            '()
            (cons (list (car var) (car expr)) (make-pairs (cdr var) (cdr expr))))))

;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+

(define empty-env
  	(lambda ()
    	(empty-env-record)))

(define extend-env
	(lambda (syms vals env)
    	(extended-env-record syms (map box vals) env)))

(define extend-env-recursively
	(lambda (names bound-to env)
		(recursively-extended-env-record names (map box bound-to) env)))

(define list-find-position
	(lambda (sym los)
    	(list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  	(lambda (pred ls)
    	(cond
    		[(null? ls) #f]
    		[(pred (car ls)) 0]
    		[else (let ((list-index-r (list-index pred (cdr ls))))
	    		(if (number? list-index-r)
					(+ 1 list-index-r)
					#f))])))

(define apply-env-ref
	(lambda (env sym succeed fail)
		(cases environment env
    		[empty-env-record () (fail)]
      		[extended-env-record (syms vals env)
				(let ((pos (list-find-position sym syms)))
      	  			(if pos
	      				(succeed (list-ref vals pos)) ; Finding associated boxed value of symbol in the vals list
	      				(apply-env-ref env sym succeed fail)))] ; Going down into the lower environment (down a level)
	    	[recursively-extended-env-record (names vals old-env) ;These might not need to be boxed, not sure yet
				(let ([pos (list-find-position sym names)])
					(if pos
						(let ([ls-ref (deref (list-ref vals pos))])
							(cases expression ls-ref
								[lambda-exp (vars bodies)
									(cond 
										[(symbol? vars) (box (sym-closure vars bodies env))]
										[(list? vars) (box (prop-closure vars bodies env))]
										[else (box (imp-closure vars bodies env))])]
								[trace-lambda-exp (name vars bodies)
									(cond 
										[(symbol? vars) (box (trace-sym-closure name vars bodies env))]
										[(list? vars) (box (trace-prop-closure name vars bodies env))]
										[else (box (trace-imp-closure name vars bodies env))])]
								[case-lambda-exp (vars-cases body-cases)
									(box (case-closure vars-cases body-cases env))]
								[else (box (prop-closure '() (list ls-ref) env))]))
						(apply-env-ref old-env sym succeed fail)))])))

(define deref unbox)

(define set-ref! set-box!)

(define apply-env
	(lambda (env var succeed fail)
		(let ([val (apply-env-ref env var succeed fail)])
			(if (box? val)
				(deref val)
				val))))

;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+

(define syntax-expand
	(lambda (expr)
		(cases expression expr
			[lit-exp (id) expr]
			[var-exp (id) expr]
			[if-exp (condition true) 
				(if-exp (syntax-expand condition) 
						(syntax-expand true))]
			[if-else-exp (condition true false)
				(if-else-exp (syntax-expand condition)
							 (syntax-expand true)
							 (syntax-expand false))]
			[lambda-exp (vars bodies) 
				(lambda-exp vars (map syntax-expand bodies))]
			[ref-lambda-exp (vars bodies)
				(ref-lambda-exp vars (map syntax-expand bodies))]
			[let-exp (bound bound-to bodies)
				(app-exp (cons (lambda-exp bound (map syntax-expand bodies))
					(map syntax-expand bound-to)))]
			[let*-exp (bound bound-to bodies)
				(if (null? (cdr bound))
					(syntax-expand (let-exp (list (car bound))
											(list (car bound-to))
											bodies)) 
				 	(syntax-expand (let-exp (list (car bound))
											(list (car bound-to))
											(list (let*-exp (cdr bound) 
															(cdr bound-to) bodies)))))]
			[named-let-exp (name bound bound-to bodies)
				(syntax-expand (letrec-exp (list name) 
					(list (lambda-exp bound bodies)) 
					(list (app-exp (cons (parse-exp name) bound-to)))))]
			[letrec-exp (names bound-to bodies)
				(letrec-exp names (map syntax-expand bound-to)
					(map syntax-expand bodies))]
			[set!-exp (var new-val)
				(set!-exp var (syntax-expand new-val))]
			[when-exp (test bodies) 
				(when-exp (syntax-expand test) (map syntax-expand bodies))]
			[cond-exp (tests bodies)
				(cond 
					[(null? (cdr tests))
						(cases expression (car tests)
							[var-exp (datum)
								(if (eq? datum 'else)
									(syntax-expand (begin-exp (car bodies)))
									(syntax-expand (if-exp (car tests) (begin-exp (car bodies)))))]
							[else 
								(syntax-expand (if-exp (car tests) (begin-exp (car bodies))))])]
					[else (syntax-expand (if-else-exp
							(car tests)
							(begin-exp (car bodies))
							(cond-exp (cdr tests) (cdr bodies))))])]
			[begin-exp (bodies) 
				(syntax-expand (let-exp '() '() bodies))]
           	[and-exp (bodies) 
           		(cond 
           			[(null? bodies) (lit-exp #t)]
           			[(null? (cdr bodies)) (car bodies)]
           			[else 
           				(syntax-expand
           					(let-exp
           						(list 'and)
           						(list (car bodies))
           						(list (if-else-exp
           							(var-exp 'and)
           							(and-exp (cdr bodies))
           							(var-exp 'and)))))])]
           	[or-exp (bodies) 
           		(cond 
           			[(null? bodies) (lit-exp #f)]
           			[(null? (cdr bodies)) (car bodies)]
           			[else 
           				(syntax-expand
           					(let-exp
           						(list 'or)
           						(list (car bodies))
           						(list (if-else-exp
           							(var-exp 'or)
           							(var-exp 'or)
           							(or-exp (cdr bodies))))))])]
           	[while-exp (condition bodies)
           		(syntax-expand (named-let-exp
           			'while
           			(list 'condition)
           			(list condition)
           			(list (if-exp condition
           				(begin-exp (append bodies (list (app-exp (list (var-exp 'while) condition)))))))))]
           	[for-loop-exp (init test update bodies)
           		(syntax-expand (app-exp (list (lambda-exp '()
           			(list init (while-exp test (append bodies (list update))))))))]
           	[case-exp (value cases bodies)
           		(cond 
           			[(null? (cdr cases))
           				(if (eq? (car cases) 'else)
           					(syntax-expand (begin-exp (car bodies)))
           					(syntax-expand (if-exp 
           						(parse-exp `(member ,(unparse-exp value) ',(car cases)))
           						(begin-exp (car bodies)))))]
           			[else 
           				(syntax-expand (if-else-exp 
           					(parse-exp `(member ,(unparse-exp value) ',(car cases)))
           					(begin-exp (car bodies))
           					(case-exp value (cdr cases) (cdr bodies))))])]
           	[trace-lambda-exp (name vars bodies)
           		(trace-lambda-exp name vars (map syntax-expand bodies))]
           	[case-lambda-exp (vars-cases body-cases)
           		(case-lambda-exp vars-cases (map (lambda (ls) (map syntax-expand ls)) body-cases))]
           	[define-exp (name value)
           		(define-exp name (syntax-expand value))]
			[app-exp (exprs) (app-exp (map syntax-expand exprs))])))

;-------------------+
;                   |
;   INTERPRETER     |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment

(define top-level-eval
	(lambda (parsed-form)
		; later we may add things that are not expressions.
		(eval-exp parsed-form (empty-env))))

; eval-exp is the main component of the interpreter

(define eval-exp
	(let ([identity-proc (lambda (x) x)])
		(lambda (expr env)
			(cases expression expr
				[lit-exp (datum) datum]
				[var-exp (id)
					(apply-env env id
						identity-proc 
						(lambda () 
							(apply-env global-env id 
								identity-proc
								(lambda () 
									(eopl:error 'apply-env 
										"variable not found in environment: ~s" id)))))]
				[letrec-exp (names bound-to bodies)
					(eval-bodies bodies (extend-env-recursively names bound-to env))]
				[set!-exp (var new-value)
					(set-ref!
						(apply-env-ref env var ;look up its ref.
							identity-proc ; procedure to call if id is in the environment 
							(lambda () 
								(apply-env-ref global-env var 
									identity-proc
									(lambda () 
										(eopl:error 'apply-env-ref 
											"variable not found in environment: ~s" var)))))
						(eval-exp new-value env))]
				[if-exp (condition true)
					(if (eval-exp condition env)
						(eval-exp true env))]
				[if-else-exp (condition true false)
					(if (eval-exp condition env) 
						(eval-exp true env) 
						(eval-exp false env))]
				[lambda-exp (vars bodies)
					(cond 
						[(list? vars) (prop-closure vars bodies env)]
						[(symbol? vars) (sym-closure (list vars) bodies env)]
						[else (imp-closure 
								(let loop ([ls vars])
									(if (symbol? ls)
										(list ls)
										(cons (car ls) (loop (cdr ls))))) 
								bodies env)])]
				[ref-lambda-exp (vars bodies)
					(ref-closure vars bodies env)]
				[when-exp (test bodies)
					(if (eval-exp test env) (eval-bodies bodies env))]
				[trace-lambda-exp (name vars bodies)
					(cond 
						[(list? vars) (trace-prop-closure name vars bodies env)]
						[(symbol? vars) (trace-sym-closure name (list vars) bodies env)]
						[else (trace-imp-closure name
								(let loop ([ls vars])
									(if (symbol? ls)
										(list ls)
										(cons (car ls) (loop (cdr ls))))) 
								bodies env)])]
				[case-lambda-exp (vars-cases body-cases)
					(case-closure vars-cases body-cases env)]
				[define-exp (name value)
					(extend-global name value)]
				[app-exp (exprs)
					(let ([proc-value (eval-exp (car exprs) env)])
						(cases proc-val proc-value
							[ref-closure (vars bodies envr)
								(apply-proc proc-value (split-ref-norm vars (cdr exprs) env))]
							[else (let ([args (eval-rands (cdr exprs) env)])
									(apply-proc proc-value args))]))]
				[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)]))))

(define split-ref-norm
	(lambda (vars args env)
		(let loop ([vars vars] [args args] 
				   [ref-vars '()] [norm-vars '()]
				   [ref-vals '()] [norm-vals '()])
			(cond 
				[(null? vars) 
					(list ref-vars 
						norm-vars 
						ref-vals 
						norm-vals)]
				[(list? (car vars))
					(loop (cdr vars) (cdr args) 
						(cons (cadar vars) ref-vars) 
						norm-vars 
						(cons (apply-env-ref env (cadr (car args)) (lambda (x) x)
								(lambda () 
									(apply-env-ref global-env (cadr (car args)) (lambda (x) x)
										(lambda () (eopl:error 'split-ref-norm "Shouldn't happen"))))) 
							ref-vals) 
						norm-vals)]
				[else
					(loop (cdr vars) (cdr args) 
						ref-vars 
						(cons (car vars) norm-vars)
						ref-vals 
						(cons (apply-env env (cadr (car args)) (lambda (x) x)
								(lambda () 
									(apply-env global-env (cadr (car args)) (lambda (x) x)
										(lambda () (eopl:error 'split-ref-norm "This also shouldn't happen")))))
							 norm-vals))]))))

; evaluate the list of operands, putting results into a list

(define eval-rands
	(lambda (rands env)
		(map (lambda (x) (eval-exp x env)) rands)))
		
;evaluate the list of bodies, returning the result of the last
(define eval-bodies
	(lambda (bodies env)
		(if (null? (cdr bodies))
			(eval-exp (car bodies) env)
			(begin
				(eval-exp (car bodies) env)
				(eval-bodies (cdr bodies) env)))))

(define apply-proc
	(lambda (proc-value args)
		(cases proc-val proc-value
			[prim-proc (op) (apply-prim-proc op args)]
			[prop-closure (vars bodies env)
				(let ([new-env (extend-env vars args env)])
					(eval-bodies bodies new-env))]
			[sym-closure (vars bodies env)
				(let ([new-env (extend-env vars (list args) env)])
					(eval-bodies bodies new-env))]
			[imp-closure (vars bodies env)
				(let ([new-env 
						(extend-env vars 
							(let loop ([vars-len (sub1 (length vars))]
									   [index 0]
									   [args args])
								(if (= index vars-len)
									(list args)
									(cons (car args) (loop vars-len (add1 index) (cdr args))))) 
							env)])
					(eval-bodies bodies new-env))]
			[ref-closure (vars bodies env)
				(let ([first-extend (extended-env-record (car args) (caddr args) env)])
					(let ([double-extend (extend-env (cadr args) (cadddr args) first-extend)])
						(eval-bodies bodies double-extend)))]
			[case-closure (vars-cases body-cases env)
				(let ([len (length args)])
					(let find-case ([vars-cases vars-cases] [body-cases body-cases])
						(if (= (length (car vars-cases)) len)
							(apply-proc (prop-closure (car vars-cases) 
													  (car body-cases)
													  env) 
										args)
							(find-case (cdr vars-cases) (cdr body-cases)))))]
			[trace-prop-closure (name vars bodies env)
				(set! indent-level (+ 2 indent-level))
				(display-traced-output indent-level name args)
				(let ([val (eval-bodies bodies (extend-env vars args env))])
					(display-traced-output indent-level val)
					(set! indent-level (- indent-level 2))
					val)]
			[trace-sym-closure (name vars bodies env)
				(set! indent-level (+ 2 indent-level))
				(display-traced-output indent-level name args)
				(let ([val (eval-bodies bodies (extend-env vars (list args) env))])
					(display-traced-output indent-level val)
					(set! indent-level (- indent-level 2))
					val)]
			[trace-imp-closure (name vars bodies env)
				(set! indent-level (+ 2 indent-level))
				(display-traced-output indent-level name args)
				(let ([val (eval-bodies bodies (extend-env vars 
							(let loop ([vars-len (sub1 (length vars))]
									   [index 0]
									   [args args])
								(if (= index vars-len)
									(list args)
									(cons (car args) (loop vars-len (add1 index) (cdr args))))) 
							env))])
					(display-traced-output indent-level val)
					(set! indent-level (- indent-level 2))
					val)]
			[else (eopl:error 'apply-proc
					"Attempt to apply bad procedure: ~s" 
					proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 quotient apply map zero? not = < <= > >= 
	cons car cdr caar cadr cdar cddr caaar caadr cadar cdaar caddr cdadr cddar cdddr 
	list list->vector null? assq eq? equal? atom? length list? pair? procedure? vector->list 
	vector make-vector vector-ref vector? number? symbol? set-car! set-cdr! vector-set! 
	display newline member))

(define init-env         ; for now, our initial global environment only contains 
	(extend-env            ; procedure names.  Recall that an environment associates
		*prim-proc-names*   ;  a value (not an expression) with an identifier.
		(map prim-proc      
			*prim-proc-names*)
		(empty-env)))

(define global-env init-env)

(define extend-global
	(lambda (name value)
		(cases environment global-env
			[extended-env-record (vars vals env)
				(set! global-env (extended-env-record (cons name vars) 
					(cons (box (eval-exp value global-env)) vals) (empty-env)))]
			[else (eopl:error 'extend-global "This should NEVER happen")])))

(define reset-global-env
	(lambda ()
		(set! global-env init-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
	(lambda (prim-proc args)
		(case prim-proc
			[(+) 
				(cond 
					[(or (null? args) (ormap (lambda (x) (not (number? x))) args))
						(eopl:error 'apply-prim-proc
							"~s arguments must be numbers" prim-proc)]
					[else (apply + args)])]
			[(-) 
				(cond 
					[(null? args) 
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (ormap number? args))
						(eopl:error 'apply-prim-proc
							"~s arguments must be numbers"
							prim-proc)]
					[else (apply - args)])]
			[(*) (cond 
					[(not (or (null? args) (ormap number? args)))
						(eopl:error 'apply-prim-proc
							"~s arguments must be numbers" prim-proc)]
					[else (apply * args)])]
			[(/) 
				(cond 
					[(null? args)
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (ormap number? args))
						(eopl:error 'apply-prim-proc
							"~s arguments must be numbers" prim-proc)]
					[else (apply / args)])]
			[(add1) 
				(cond 
					[(not (null? (cdr args)))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (number? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a number" prim-proc)]
					[else (+ (car args) 1)])]
			[(sub1)
				(cond 
					[(not (null? (cdr args)))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (number? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a number" prim-proc)]
					[else (- (car args) 1)])]
			[(quotient)
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"~s must have two arguments" prim-proc)]
					[(not ((list-of number?) args))
						(eopl:error 'apply-prim-proc
							"~s arguments must be numbers" prim-proc)]
					[else (quotient (car args) (cadr args))])]
			[(apply)
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (proc-val? (car args)))
						(eopl:error 'apply-prim-proc
							"~s car must be procedure" prim-proc)]
					[else (apply-proc (car args) (cadr args))])]
			[(map)
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (proc-val? (car args)))
						(eopl:error 'apply-prim-proc
							"~s car must be procedure" prim-proc)]
					[else 
						(map (lambda (x) (apply-proc (car args) (list x))) (cadr args))])]
			[(zero?) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (number? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a number" prim-proc)]
					[else (zero? (car args))])]
			[(not) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (not (car args))])]
			[(=) 
				(cond 
					[(null? args)
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (ormap number? args))
						(eopl:error 'apply-prim-proc
							"~s arguments must be numbers" prim-proc)]
					[else (apply = args)])]
			[(<) 
				(cond 
					[(null? args)
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to <" prim-proc)]
					[(not (ormap real? args))
						(eopl:error 'apply-prim-proc
							"~s arguments must be real numbers" prim-proc)]
					[else (apply < args)])]
			[(<=) 
				(cond 
					[(null? args)
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (ormap real? args))
						(eopl:error 'apply-prim-proc
							"~s arguments must be real numbers" prim-proc)]
					[else (apply <= args)])]
			[(>) 
				(cond 
					[(null? args)
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (ormap real? args))
						(eopl:error 'apply-prim-proc
							"~s arguments must be real numbers" prim-proc)]
					[else (apply > args)])]
			[(>=) 
				(cond 
					[(null? args)
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (ormap real? args))
						(eopl:error 'apply-prim-proc
							"~s arguments must be real numbers" prim-proc)]
					[else (apply >= args)])]
			[(cons)
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (cons (car args) (cadr args))])]
			[(car) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[else (car (car args))])]
			[(cdr) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[else (cdr (car args))])]
			[(caar) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (car (car args))))
						(eopl:error 'apply-prim-proc
							"~s: car argument must be a pair" prim-proc)]
					[else (caar (car args))])]
			[(cadr) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (cdr (car args))))
						(eopl:error 'apply-prim-proc
							"~s:  car argument must be a pair" prim-proc)]
					[else (cadr (car args))])]
			[(cdar)
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (car (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cdr argument must be a pair" prim-proc)]
					[else (cdar (car args))])]
			[(cddr) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (cdr (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cdr argument must be a pair" prim-proc)]
					[else (cddr (car args))])]
			[(caaar) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (car (car args))))
						(eopl:error 'apply-prim-proc
							"~s: caar argument must be a pair" prim-proc)]
					[(not (pair? (caar (car args))))
						(eopl:error 'apply-prim-proc
							"~s: car argument must be a pair" prim-proc)]
					[else (caaar (car args))])]
			[(caadr) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (cdr (car args))))
						(eopl:error 'apply-prim-proc
							"~s: caar argument must be a pair" prim-proc)]
					[(not (pair? (cadr (car args))))
						(eopl:error 'apply-prim-proc
							"~s: car argument must be a pair" prim-proc)]
					[else (caadr (car args))])]
			[(cadar) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (car (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cadr argument must be a pair" prim-proc)]
					[(not (pair? (cdar (car args))))
						(eopl:error 'apply-prim-proc
							"~s: car argument must be a pair" prim-proc)]
					[else (cadar (car args))])]
			[(cdaar) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (car (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cdar argument must be a pair" prim-proc)]
					[(not (pair? (caar (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cdr argument must be a pair" prim-proc)]
					[else (cdaar (car args))])]
			[(caddr) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (cdr (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cadr argument must be a pair" prim-proc)]
					[(not (pair? (cddr (car args))))
						(eopl:error 'apply-prim-proc
							"~s: car argument must be a pair" prim-proc)]
					[else (caddr (car args))])]
			[(cdadr) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (cdr (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cdar argument must be a pair" prim-proc)]
					[(not (pair? (cadr (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cdr argument must be a pair" prim-proc)]
					[else (cdadr (car args))])]
			[(cddar) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (car (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cddr argument must be a pair" prim-proc)]
					[(not (pair? (cdar (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cdr argument must be a pair" prim-proc)]
					[else (cddar (car args))])]
			[(cdddr) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[(not (pair? (cdr (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cddr argument must be a pair" prim-proc)]
					[(not (pair? (cddr (car args))))
						(eopl:error 'apply-prim-proc
							"~s: cdr argument must be a pair" prim-proc)]
					[else (cdddr (car args))])]
			[(list) args]
			[(null?) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (null? (car args))])]
			[(assq) 
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (or (literal? (car args)) (pair? (car args)) (null? (car args))))
						(eopl:error 'apply-prim-proc
							"First arg to ~s must be a literal, pair, or null" prim-proc)]
					[(not ((list-of pair?) (cadr args)))
						(eopl:error 'apply-prim-proc
							"Second arg to ~s must be a list of pairs" prim-proc)]
					[else (assq (car args) (cadr args))])]
			[(eq?) 
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (eq? (car args) (cadr args))])]
			[(equal?) 
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (equal? (car args) (cadr args))])]
			[(atom?) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (atom? (car args))])]
			[(length) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (list? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a iist" prim-proc)]
					[else (length (car args))])]
			[(list->vector) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (list? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a iist" prim-proc)]
					[else (list->vector (car args))])]
			[(list?) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (list? (car args))])]
			[(pair?) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (pair? (car args))])]
			[(procedure?)
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (proc-val? (car args))])]
			[(vector->list) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (vector? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a vector" prim-proc)]
					[else (vector->list (car args))])]
			[(vector) (apply vector args)]
			[(make-vector) 
				(cond 
					[(or (null? args) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(or (not (integer? (car args))) (> 0 (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a non-negative integer" prim-proc)]
					[(null? (cdr args))
						(make-vector (car args))]
					[else (make-vector (car args) (cadr args))])]
			[(vector-ref) 
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(or (not (integer? (cadr args))) (not (vector? (car args))) (> 0 (cadr args)))
						(eopl:error 'apply-prim-proc
							"~s arguments must be a vector and non-negative integer" prim-proc)]
					[else (vector-ref (car args) (cadr args))])]
			[(vector?) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (vector? (car args))])]
			[(number?) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (number? (car args))])]
			[(symbol?) 
				(cond 
					[(or (null? args) (not (null? (cdr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[else (symbol? (car args))])]
			[(set-car!) 
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[else (set-car! (car args) (cadr args))])]
			[(set-cdr!) 
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of arguments to ~s" prim-proc)]
					[(not (pair? (car args)))
						(eopl:error 'apply-prim-proc
							"~s argument must be a pair" prim-proc)]
					[else (set-cdr! (car args) (cadr args))])]
			[(vector-set!) 
				(cond 
					[(or (null? args) (null? (cdr args)) (null? (cddr args)) (not (null? (cdddr args))))
						(eopl:error 'apply-prim-proc
							"Incorrect number of args to ~s" prim-proc)]
					[(not (vector? (car args)))
						(eopl:error 'apply-prim-proc
							"~s first arg must be a vector" prim-proc)]
					[(or (not (integer? (cadr args))) (> 0 (cadr args)) (>= (cadr args) (vector-length (car args))))
						(eopl:error 'apply-prim-proc
							"~s second arg must be 0 <= arg < length" prim-proc)]
					[else (vector-set! (car args) (cadr args) (caddr args))])]
			[(display) 
				(cond 
					[(or (null? args) (not (null? (cdr args)))) 
						(eopl:error 'apply-prim-proc 
							"~s must have 1 argument" prim-proc)]
					[else (display args)])]
			[(newline) 
				(cond 
					[(not (null? args)) 
						(eopl:error 'apply-prim-proc 
							"~s cannot have any arguments" prim-proc)]
					[else (newline)])]
			[(member)
				(cond 
					[(or (null? args) (null? (cdr args)) (not (null? (cddr args))))
						(eopl:error 'apply-prim-proc 
							"incorrect number of arguments to ~s" prim-proc)]
					[(not (list? (cadr args)))
						(eopl:error 'apply-prim-proc 
							"second argument to ~s must be a list" prim-proc)]
					[else (member (car args) (cadr args))])]
			[else (eopl:error 'apply-prim-proc 
					"Bad primitive procedure name: ~s" 
					prim-proc)])))

(define rep      ; "read-eval-print" loop.
	(lambda ()
		(display "--> ")
		(set! indent-level 0)
		(set! p (open-output-file (string-append 
			"C:/Users/Public/TestOutput" (number->string eval-count) ".txt")))
		(set! eval-count (+ 1 eval-count))
		;; notice that we don't save changes to the environment...
		(let ([answer (top-level-eval (syntax-expand (parse-exp (read))))])
		;; TODO: are there answers that should display differently?
			(cond 
				[(proc-val? answer) (eopl:pretty-print '<interpreter-procedure>)]
				[else (eopl:pretty-print answer)])
			(newline)
			(close-output-port p)
			(rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
	(lambda (x) 
		(set! indent-level 0)
		(top-level-eval (syntax-expand (parse-exp x)))))