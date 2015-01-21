(load "chez-init.ss") 



;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+



;; Parsed expression datatypes
(define valid-lambda-args? 
	(lambda (args)
		(if (pair? args)
			(or 
				(and 		; by-value args
					(symbol? (car args)) 
					(valid-lambda-args? (cdr args)))
				(and 		; by-ref args
					(pair? (car args)) 
					(equal? (caar args) 'ref) 
					(symbol? (cadar args))
					(valid-lambda-args? (cdr args))))
			(or (symbol? args) (null? args))
		)
	))

(define literal? 
	(lambda (x) 
		(or (integer? x) 
			(string? x) 
			(boolean? x) 
			(vector? x))
	))
	
(define qexp? 
	(lambda (x) 
		#t))
(define-datatype expression expression?
	(var-exp
		(id symbol?))
	(t-exp)
	(f-exp)
	(quoted-exp 
		(expr qexp?))
	(vect-exp 
		(vect vector?))
	(int-exp
		(val integer?))
	(string-exp 
		(str string?))
	(lambda-exp
		(id valid-lambda-args?)
		(bodies expression?))
	(app-exp
		(rator expression?)
		(rand expression?))
	(let-exp
		(def expression?)
		(bodies expression?))
	(let*-exp
		(def expression?)
		(bodies expression?))
	(letrec-exp
		(def expression?)
		(bodies expression?))
	(namedlet-exp
		(name symbol?)
		(def expression?)
		(bodies expression?))
	(set!-exp
		(name symbol?)
		(value expression?))
	(if1-exp
		(test expression?)
		(body expression?))
	(if2-exp
		(test expression?)
		(body expression?)
		(elsebody expression?)
	)
	(letval
		(name symbol?)
		(value expression?)
		(rest expression?))
	(null-exp)
	(cond-exp
		(tests (list-of expression?)))
	(and-exp
		(tests (list-of expression?)))
	(or-exp
		(tests (list-of expression?)))
	(begin-exp
		(bodies expression?))
	(case-exp
		(value expression?)
		(bodies (list-of expression?)))
	(while-exp
		(test expression?)
		(bodies (list-of expression?))
	)
	(define-exp
		(name symbol?)
		(value expression?)
	)
	(void-exp)
)
;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
	(empty-env-record)
	(extended-env-record
		(syms (lambda (x) ((list-of lambda-arg?) x)))
		(vals (list-of scheme-value?))
		(env environment?)
	)
)
; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
	[prim-proc
		(name symbol?)
	]
	[closure
		(params (list-of lambda-arg?))
		(bodies (list-of expression?))
		(env environment?)
	]
	[closure-indefinite
		(param symbol?)
		(bodies (list-of expression?))
		(env environment?)
	]
	[closure-mixed
		(params (list-of symbol?))
		(iparam symbol?)
		(bodies (list-of expression?))
		(env environment?)
	]
)

(define-datatype reference reference?
	[ref 
		(var symbol?)
		(env environment?)
	]
)

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.

(define get-let-ids (lambda (ex)
	(cases expression ex 
		[letval (name value rest)
			(cons name (get-let-ids rest))]
		[null-exp () '()]
		[else ex]
	)
))
(define get-let-vars (lambda (ex env)
	(cases expression ex 
		[letval (name value rest)
			(cons (eval-exp value env) (get-let-vars rest env))]
		[null-exp () '()]
		[else ex]
	)
))
(define let-args-valid? (lambda (args) 
	(cond 
		[(and (pair? args) (not (list? args)))
			(eopl:error 'parse-exp "Improper list in let arguments")]
		[(and (pair? args) (pair? (car args))(not (list? (car args))))
			(eopl:error 'parse-exp "Improper list in let declarations")]
		[(and (pair? args) (pair? (car args)) (not(= (length(car args)) 2)))
			(eopl:error 'parse-exp "Wrong length in let declaration")]
		[(and (pair? args) (pair? (car args)) (not (symbol? (caar args))))
			(eopl:error 'parse-exp "Let has non-symbol declaration")]
		[(and (pair? args) (pair? (car args)) (is-exp-parse-errors? (cadar args)) (let-args-valid? (cdr args)))
			#t]
		[(null? args)
		#t]
		[else (eopl:error 'parse-exp "misc. error in let declaration")]
	)))
	
(define ref? 
	(lambda (x)
		(and 
			(pair? x)
			(equal? (car x) 'ref)
			(symbol? (cadr x)))
	))
	
(define lambda-arg?
	(lambda (param)
		(or (symbol? param) (ref? param))
	))

(define is-exp-parse-errors? (lambda (datum) 
	(cond 
		[(symbol? datum)
			#t]
		[(literal? datum)
			#t]
			
		[(and (pair? datum) (not (list? datum))) 
			(eopl:error 'parse-exp "application of improper list")]
			
		;Lambda checks
		[(and (pair? datum) (equal? 'lambda (car datum)) (<= (length datum) 2))
			(eopl:error 'parse-exp "Insufficient arguments to lambda: missing body")]				;All lambdas with 1-2 length
		[(and (pair? datum) (equal? 'lambda (car datum)) (not(valid-lambda-args? (cadr datum))))
			(eopl:error 'parse-exp "Invalid lambda formals: not all symbols")]
		[(and (pair? datum) (equal? 'lambda (car datum)) (is-exp-parse-errors? (caddr datum)))
			#t]
		
		;If checks
		[(and (pair? datum) (equal? 'if (car datum)) (= (length datum) 1))
			(eopl:error 'parse-exp "Insufficient arguments for if: no test")]
		[(and (pair? datum) (equal? 'if (car datum)) (= (length datum) 2))
			(eopl:error 'parse-exp "Insufficient arguments for if: no body")]
		[(and (pair? datum) (equal? 'if (car datum)) (>= (length datum) 5))
			(eopl:error 'parse-exp "Too many arguments for if: at most 3 should be used")]
		[(and (pair? datum) (equal? 'if (car datum)) (is-exp-parse-errors? (cdr datum)))
			#t]
		
		;let including named let checks
		[(and (pair? datum) (equal? 'let (car datum)) (= (length datum) 1))
			(eopl:error 'parse-exp "No arguments passed to let")]
		[(and (pair? datum) (equal? 'let (car datum)) (= (length datum) 2))
			(eopl:error 'parse-exp "No body in let")]
		[(and (pair? datum) (equal? 'let (car datum)) (= (length datum) 3) (not (list? (cadr datum))))
			(eopl:error 'parse-exp "No body in named let")]
		[(and 
			(pair? datum) 
			(equal? 'let (car datum))
			(list? (cadr datum))
			(let-args-valid? (cadr datum)) 
			(is-exp-parse-errors? (caddr datum)))
			#t]
		[(and
			(pair? datum)
			(equal? 'let (car datum))
			(not(list? (cadr datum)))
			(not(symbol? (cadr datum))))
			(eopl:error 'parse-exp "Named let with non-symbol name")]
		[(and
			(pair? datum)
			(equal? 'let (car datum))
			(not(list? (cadr datum)))
			(let-args-valid? (caddr datum)))
			(is-exp-parse-errors? (cadddr datum))
			#t]
		
		;letrec checks
		[(and (pair? datum) (equal? 'letrec (car datum)) (= (length datum) 1))
			(eopl:error 'parse-exp "No arguments passed to letrec")]
		[(and (pair? datum) (equal? 'letrec (car datum)) (= (length datum) 2))
			(eopl:error 'parse-exp "No body in letrec")]
		[(and
			(pair? datum)
			(equal? 'letrec (car datum))
			(not(list? (cadr datum))))
			(eopl:error 'parse-exp "letrec has non-list declarations")]
		[(and 
			(pair? datum) 
			(equal? 'letrec (car datum))
			(list? (cadr datum))
			(let-args-valid? (cadr datum)) 
			(is-exp-parse-errors? (caddr datum)))
			#t]
			
		;let* checks
		[(and (pair? datum) (equal? 'let* (car datum)) (= (length datum) 1))
			(eopl:error 'parse-exp "No arguments passed to let*")]
		[(and (pair? datum) (equal? 'let* (car datum)) (= (length datum) 2))
			(eopl:error 'parse-exp "No body in let*")]
		[(and
			(pair? datum)
			(equal? 'let* (car datum))
			(not(list? (cadr datum))))
			(eopl:error 'parse-exp "let* has non-list declarations")]
		[(and 
			(pair? datum) 
			(equal? 'let* (car datum))
			(list? (cadr datum))
			(let-args-valid? (cadr datum)) 
			(is-exp-parse-errors? (caddr datum)))
			#t]
		
		;set! checks
		[(and (pair? datum) (equal? 'set! (car datum)) (= (length datum) 1))
			(eopl:error 'parse-exp "No arguments passed to set!")]
		[(and (pair? datum) (equal? 'set! (car datum)) (= (length datum) 2))
			(eopl:error 'parse-exp "insufficient arguments to set!, need 2")]
		[(and (pair? datum) (equal? 'set! (car datum)) (> (length datum) 3))
			(eopl:error 'parse-exp "Too many arguments passed to set!")]
		[(and (pair? datum) (equal? 'set! (car datum)) (not (symbol? (cadr datum))))
			(eopl:error 'parse-exp "Attempt to assign value to non-symbol")]
		[(and (pair? datum) (equal? 'set! (car datum)) (is-exp-parse-errors? (caddr datum)))
			#t]
			
		;quote
		[(and (pair? datum) (equal? 'quote (car datum)))
			#t]
			
		;fallback and base case
		[(and (pair? datum) (is-exp-parse-errors? (car datum)) (is-exp-parse-errors? (cdr datum)))
			#t]
		[(null? datum) 
			#t]
		[else
			(eopl:error 'parse-exp "unidentified error in parsing")
		]
)))
(define let-parse (lambda (datum) 
	(if(null? datum)
		(null-exp)
		(letval(caar datum) (syntax-expand (parse-exp (cadar datum))) (let-parse (cdr datum)))
	)
))
(define parse-exp
  (lambda (datum)
	(if	(is-exp-parse-errors? datum)
		(cond
			[(symbol? datum) (var-exp datum)]
			[(integer? datum) (int-exp datum)]
			[(string? datum) (string-exp datum)]
			[(vector? datum) (vect-exp datum)]
			[(equal? #t datum) (t-exp)]
			[(equal? #f datum) (f-exp)]
			[(pair? datum)
				(cond
				;Quoted
				[(equal? (car datum) 'quote)
					(quoted-exp (cadr datum))]
				;Lambda
				[(equal? (car datum) 'lambda)
					(lambda-exp (cadr datum) (parse-exp (cddr datum)))]
				;let
				[(and (equal? (car datum) 'let) (list? (cadr datum)))
					(let-exp (let-parse(cadr datum)) (parse-exp (cddr datum)))]
				;Named let
				[(and (equal? (car datum) 'let) (symbol? (cadr datum)))
					(namedlet-exp (cadr datum) (let-parse(caddr datum)) (syntax-expand (parse-exp (cdddr datum))))]
				;Let*
				[(equal? (car datum) 'let*)
					(let*-exp (let-parse(cadr datum)) (parse-exp (cddr datum)))]
				;Letrec
				[(equal? (car datum) 'letrec)
					(letrec-exp (let-parse(cadr datum)) (syntax-expand (parse-exp (cddr datum))))]
				;Set!
				[(equal? (car datum) 'set!)
					(set!-exp (cadr datum) (parse-exp (caddr datum)))]
				;Define
				[(equal? (car datum) 'define)
					(define-exp (cadr datum) (parse-exp (caddr datum)))
				]
				;If
				[(equal? (car datum) 'if)
					(if (= (length datum) 3)
						(if1-exp (parse-exp (cadr datum)) (parse-exp (caddr datum)))
						(if2-exp (parse-exp (cadr datum)) (parse-exp (caddr datum)) (parse-exp (cadddr datum)))
					)]
				;Cond
				[(equal? (car datum) 'cond)
					(cond-exp (map parse-exp (cdr datum)))
				]
				;Or
				[(equal? (car datum) 'or)
					(or-exp (map parse-exp (cdr datum)))]
				;And
				[(equal? (car datum) 'and)
					(and-exp (map parse-exp (cdr datum)))]
				;Begin
				[(equal? (car datum) 'begin)
					(begin-exp (parse-exp (cdr datum)))]
				;Case
				[(equal? (car datum) 'case)
					(case-exp (parse-exp (cadr datum)) (map case-parse (cddr datum)))
				]
				;While
				[(equal? (car datum) 'while)
					(while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))
				]
				;Recursion
				[else	
					(app-exp
						(parse-exp (car datum))
						(parse-exp (cdr datum))
					)]
				)
			]
			[(null? datum)
				(null-exp)]
		)
	)))
(define case-parse (lambda (ex) (app-exp (quoted-exp (car ex)) (parse-exp (cdr ex)))))
(define unparse-exp (lambda (ex)
    (cases expression ex 
		[or-exp (tests) ex]
		[and-exp (tests) (cons 'and (map unparse-exp tests))]
		[void-exp () (if #f #f)]
		[cond-exp (tests) (cons 'cond (unparse-exp ex))]
		[var-exp (id) id]
		[t-exp () #t]
		[f-exp () #f]
		[vect-exp (vect) vect]
		[int-exp (val) val]
		[string-exp	(str) str]
		[null-exp () '()]
		[begin-exp (bodies)(cons 'begin (unparse-exp bodies))]
		[lambda-exp (id bodies)
			(cons 'lambda (cons id
				(unparse-exp bodies)))]
		[app-exp (rator rand)
			(cons (unparse-exp rator) (unparse-exp rand))]
		[let-exp (def bodies)
			(cons 'let (cons (unparse-exp def) (unparse-exp bodies)))]
		[letval (name value next) 
			(cons (list name (unparse-exp value)) (unparse-exp next))]
		[namedlet-exp (name def bodies)
			(cons 'let (cons name (cons (unparse-exp def) (unparse-exp bodies))))]
		[let*-exp (def bodies)
			(cons 'let* (cons (unparse-exp def) (unparse-exp bodies)))]
		[letrec-exp (def bodies)
			(cons 'letrec (cons (unparse-exp def) (unparse-exp bodies)))]
		[set!-exp (name value)
			(list 'set! name (unparse-exp value))]
		[if1-exp (test body)
			(list 'if (unparse-exp test) (unparse-exp body))]
		[if2-exp (test body elsebody)
			(list 'if (unparse-exp test) (unparse-exp body) (unparse-exp elsebody))]
		[quoted-exp (expr) expr]
		[define-exp (name value)
			(list 'define name (unparse-exp value))
		]
		[else ex]
	)	
))







;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
      (empty-env-record ()
        (fail))
      (extended-env-record (syms vals env)
	(let ((pos (list-find-position sym syms)))
      	  (if (or (number? pos) (list? pos))
			  (succeed (list-ref vals pos))
			  (apply-env env sym succeed fail)))))))

;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+

(define null-exp? (lambda (ex)
	(cases expression ex 
		[null-exp () #t]
		[else #f]
	)
))
(define not-final-def (lambda (ex) 
	(cases expression ex 
		[letval (name value next)
			(not (null-exp? next))]
		[else #f]
		)
))
(define get-first-def (lambda (ex) 
	(cases expression ex 
		[letval (name value next)
			(letval name value (null-exp))]
		[else #f]	
	)
))
(define get-rest-def (lambda (ex)
	(cases expression ex 
		[letval (name value next)
			next]
		[else #f]	
	)
))

(define app-exp-rator (lambda (ex) 
	(cases expression ex 
		[app-exp (rator rand) rator]
		[var-exp (id) id]
		[quoted-exp (expr) expr]
		[else ex]
	)
))
(define app-exp-rand (lambda (ex)
	(cases expression ex 
		[app-exp (rator rand) rand]
		[var-exp (id) id]
		[else ex]
	)
))
(define syntax-expand (lambda (ex) 
	(cases expression ex 
		[or-exp (tests) 
			(if (null? tests)
				(f-exp)
				(syntax-expand 
					(let-exp (letval 'lkjadsflkjdsalkfjsadlkjasdhfkjalsdhfkjasdhflkajsdhfakljsfd (car tests) (null-exp))
					(app-exp (if2-exp (var-exp 'lkjadsflkjdsalkfjsadlkjasdhfkjalsdhfkjasdhflkajsdhfakljsfd)
							 (var-exp 'lkjadsflkjdsalkfjsadlkjasdhfkjalsdhfkjasdhflkajsdhfakljsfd)
							 (syntax-expand (or-exp (cdr tests)))
					)
					(null-exp))
				)
			
		))]
		[define-exp (name value)
			(define-exp name (syntax-expand value))
		]
		[and-exp (tests)
			(if (null? (cdr tests))
				(car tests)
				(if2-exp (car tests)
							 (syntax-expand (and-exp (cdr tests)))
							 (f-exp)
		))]
		
		[cond-exp (tests) 
			(if (not (null? tests))
				(if (equal? (app-exp-rator (app-exp-rator (car tests))) 'else)
					(syntax-expand (app-exp-rator (app-exp-rand (car tests))))
					(syntax-expand (if2-exp (app-exp-rator (car tests)) 
						(app-exp-rator (app-exp-rand (car tests)))
						(syntax-expand (cond-exp (cdr tests)))
					))
				)
				(void-exp)
			)
		]
		
		[begin-exp (bodies)
			(if (null? bodies)
				(void-exp)
				(syntax-expand (app-exp (lambda-exp '() bodies) (null-exp)))
			)
				
		]
		[lambda-exp (id bodies)
			(lambda-exp id (syntax-expand bodies))]
		[app-exp (rator rand)
			(app-exp (syntax-expand rator) (syntax-expand rand))]
		[let-exp (def bodies)
			(app-exp (lambda-exp 
						(get-let-ids def) 
						(syntax-expand bodies)) 
				(get-let-vars-stx def))]
		[if1-exp (test body)
			(if1-exp (syntax-expand test) (syntax-expand body))]
		[if2-exp (test body elsebody)
			(if2-exp (syntax-expand test) 
				(syntax-expand body) 
				(syntax-expand elsebody))]
		[let*-exp (def bodies)
			(if (not-final-def def)
				(syntax-expand
					(let-exp (get-first-def def)
						(app-exp (syntax-expand (let*-exp (get-rest-def def) bodies))(null-exp))
					)
				)
				(syntax-expand 
					(let-exp def bodies)
				)
			)
		]
		[case-exp (value bodies)
			(if (not (null? bodies))
				(if (equal? (app-exp-rator (app-exp-rator (car bodies))) 'else)
					(syntax-expand (app-exp-rator (app-exp-rand (car bodies))))
					(syntax-expand (if2-exp 
						(app-exp 
							(var-exp 'member)
							(app-exp 
								value
								(app-exp 
									(app-exp-rator (car bodies))
									(null-exp)
								)
							)
						)
						(app-exp-rator (app-exp-rand (car bodies)))
						(syntax-expand (case-exp value (cdr bodies)))
					))
				)
				(void-exp)
			)
			]
		[namedlet-exp (name def bodies) 
			(syntax-expand
				(letrec-exp 
					(letval
						name
						(lambda-exp (get-let-ids def) (syntax-expand bodies))
						(null-exp)
					)
					(app-exp (app-exp (var-exp name) (get-let-vars-stx def)) (null-exp))
				)
			)
		]
		[set!-exp (name value) 
			(set!-exp name (syntax-expand value))]
		[else ex]
	)
))
(define get-let-vars-stx (lambda (ex)
	(cases expression ex 
		[letval (name value rest)
			(app-exp (syntax-expand value) (get-let-vars-stx rest))]
		[else ex]	
	)
))



;-------------------+
;                   |
;   INTERPRETER     |
;                   |
;-------------------+
(define list-from-app (lambda (app) 
	(cases expression app
		[null-exp () '()]
		[app-exp (rator rand)
			(cons rator (list-from-app rand))]
		[else app]
	)
))


; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp (syntax-expand form) init-env)
))

(define ordered-map (lambda (func ls built) 
	(if (null? ls) built
		(ordered-map 
			func 
			(cdr ls) 
			(cons (func (car ls)) built)
	))
))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (xp env)
    (cases expression xp
		[while-exp (test bodies) 
			(let loop ()
				(if (eval-exp test env)
					(begin
						(ordered-map (lambda (x) (eval-exp x env)) bodies '())
						(loop)
			)))]
					
		[and-exp (tests) xp]
		[or-exp (tests) xp]
		[cond-exp (tests) xp]
		[t-exp () #t]
		[f-exp () #f]
		[vect-exp (vect) vect]
		[int-exp (val) val]
		[string-exp (str) str]
		[var-exp (id)
			(apply-env env id ; look up its value.
				(lambda (x) (if (reference? x) 
								(apply-env (caddr x) (cadr x) 
									(lambda (x) x)
									(lambda () (eopl:error 'apply-env ; procedure to call if id not in env
													"variable not found in environment: ~s"
													id)))
								x)) ; procedure to call if id is in the environment 
				(lambda () (apply-env init-env id 
								(lambda (x) x)
								(lambda () (eopl:error 'apply-env ; procedure to call if id not in env
									"variable not found in environment: ~s"
									id)
							))
				))]
		[let-exp (def bodies)
			(let ([new-env (extend-env 
								(get-let-ids def)
								(get-let-vars def env)
								env)])
				(let ((bodies (list-from-app bodies)))
					(let loop([bodies bodies])
						(if (null? (cdr bodies))
							(eval-exp (car bodies) new-env)
							(begin (eval-exp (car bodies) new-env)
								(loop (cdr bodies))
				))))
			)]
		[if1-exp (test body)
			(if (eval-exp test env)
				(eval-exp body env))]
		[if2-exp (test body elsebody)
			(if (eval-exp test env)
				(eval-exp body env)
				(eval-exp elsebody env))]
		[lambda-exp (params body)
			(let ((bodies (list-from-app body)))
				(if (symbol? params)
					(closure-indefinite params bodies env)
					(if (list? params)
						(let ([refed-params (parse-refs params env)])
							(closure refed-params bodies env))
						(closure-mixed (truncate-improper params)
									   (get-improper-last params)
									   bodies env)
					)))]
		[app-exp (rator rand)
			(let ([proc-value (eval-exp rator env)]
					[args (eval-rands rand env)])
				(apply-proc proc-value args))]
		[letrec-exp (def bodies)
			(let ([let-ids (get-let-ids def)] 
					[let-vars (map (lambda (x) x) '(fdsafdsafelkjfdsjfdfdsfdsj fdsafdsafdsajfsafdsapoijfsa))]
				)
				(let ([new-env (extend-env 
								let-ids
								let-vars
								env)])
					(set-car! let-vars (car (get-let-vars def new-env)))
					(set-cdr! let-vars (cdr (get-let-vars def new-env)))
					(let ((bodies (list-from-app bodies)))
						(let loop([bodies bodies])
							(if (null? (cdr bodies))
								(eval-exp (car bodies) new-env)
								(begin (eval-exp (car bodies) new-env)
									(loop (cdr bodies))
								)
							)
						)
					)
					
				)
			)
		]
		[null-exp () '()]
		[quoted-exp (expr) expr]
		[void-exp () (if #f #f)]
		[set!-exp (name value) 
			(let ([x (apply-env env name ; look up its value.
						(lambda (x) x) ; procedure to call if id is in the environment 
						(lambda () (apply-env init-env name 
										(lambda (x) x)
										(lambda () (eopl:error 'apply-env ; procedure to call if id not in env
											"variable not found in environment: ~s"
											id)
									))
						))])
				(if (reference? x)
					(set!-helper-parsed (cadr x) value (caddr x) env)
					(set!-helper-parsed name value env env)
					
				))]
		[define-exp (name value)
			(define-helper-parsed name value env)
		]
		[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" xp)])))
		
(define parse-refs
	(lambda (params env)
		(cond 
			[(not (pair? params))
				params]
			[(null? params)
				'()]
			[(ref? (car params))
				(cons (ref (cadar params) env)
					  (parse-refs (cdr params) env))]
			[else 
				(cons (car params) (parse-refs (cdr params) env))]
		)))
		
(define define-helper-parsed 
	(lambda (name val env1)
		(cases environment init-env
			
			(empty-env-record ()
				(fail))
			(extended-env-record (syms vals env)
				(begin
					(set-cdr! syms (cons (car syms) (cdr syms)))
					(set-car! syms name)
					(set-cdr! vals (cons (car vals) (cdr vals)))
					(set-car! vals (eval-exp val env1))
			)))
	))
	
(define set!-helper-parsed 
	(lambda (name val env1 low-env)
		(cases environment env1
			(empty-env-record ()
				(fail))
			(extended-env-record (syms vals env)
				(let ((pos (list-find-position name syms)))
					(if (equal? pos #f)
					(set!-helper-parsed name val env low-env)
					(set-car! (list-ref-rest vals pos) (eval-exp val low-env)))
			)))
	))

(define list-ref-rest
  (lambda (ls n)
    (if (= n 0)
        ls
        (list-ref-rest (cdr ls) (- n 1)))))
		
		
		
		
		
(define truncate-improper 
	(lambda (x) 
		(if (pair? (cdr x))
			(cons(car x) (truncate-improper (cdr x)))
			(list (car x))
		)))
	
(define get-improper-last 
	(lambda (x)
		(if (pair? x)
			(get-improper-last (cdr x))
			x
		)))
; evaluate the list of operands, putting results into a list

(define eval-rands
	(lambda (rands env)
		(cases expression rands
			[null-exp () '()]
			[app-exp (rator rand) 
				(cons (eval-exp rator env) 
					  (eval-rands rand env))]
			[else rands]
			)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
	(lambda (proc-value args)
		(cases proc-val proc-value
			[prim-proc (op) (apply-prim-proc op args)]
			[closure (params bodies env)
				(let ((new-env (extend-env params args env)))
					(ordered-apply-proc bodies new-env))]
			[closure-indefinite (param bodies env) 
				(let ((new-env (extend-env (list param) (list args) env)))
					(ordered-apply-proc bodies new-env))]
			[closure-mixed (params iparam bodies env) 
				(let ((new-env (extend-env 
					(cons iparam params)
					(move-first-n-to-back (length params) args '())
					env
				)))	
					(ordered-apply-proc bodies new-env)
				)]
			; You will add other cases
			[else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))
					
(define move-first-n-to-back 
	(lambda (n ls built-list)
		(if(zero? n) 
			(cons ls (reverse built-list))
			(move-first-n-to-back (- n 1) (cdr ls) (cons (car ls) built-list))
		)))
		
(define ordered-apply-proc 
	(lambda (bodies env)
		(if (null? (cdr bodies))
			(eval-exp (car bodies) env)
			(begin 
				(eval-exp (car bodies) env)
				(ordered-apply-proc (cdr bodies) env)
			)
		)
	)
)
(define *prim-proc-names* 
	'(+ - *  = / add1 sub1
		zero? not = < <= > >= 
		car cdr list cons append quote 
		caar cadr cdar cddr
		caaar caadr cadar cdaar cddar cdadr cdddr 
		null? eq? eqv? equal? atom? list? pair? procedure? vector? number? symbol?
		assq length 
		vector make-vector vector-ref list->vector vector->list 
		set-car! set-cdr! vector-set! 
		display newline
		map apply not member quotient
		list-tail
		reverse
		pretty-print
		))

(define make-init-env	; for now, our initial global environment only contains 
	(lambda ()			; procedure names.  Recall that an environment associates
		(extend-env		;  a value (not an expression) with an identifier.
			(map (lambda (x) x) *prim-proc-names*)
			(map prim-proc      
				*prim-proc-names*)
			(empty-env))))
		
(define init-env (make-init-env))

(define reset-global-env
	(lambda ()
		(set! init-env (make-init-env))))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
	  [(pretty-print) (apply pretty-print args)]
      [(+) 		(apply	+ 			args)]
      [(-) 		(apply	- args)]
      [(*) 		(apply	* args)]
	  [(/) 		(apply	/ args)]
      [(add1) 	(+ 		(car args) 1)]
      [(sub1) 	(- 		(car args) 1)]
	  [(reverse) (apply reverse args)]
	  [(zero?)	(zero? 	(car args))]
	  [(not) 	(not 	(car args))]
	  [(=) 		(= 		(car args) (cadr args))]
	  [(<)		(< 		(car args) (cadr args))]
	  [(<=)		(<= 	(car args) (cadr args))]
	  [(>)		(> 		(car args) (cadr args))]
	  [(>=)		(>= 	(car args) (cadr args))]
	  
	  [(cons) 	(apply cons args)]
	  [(car)	(car	(car args))]
	  [(cdr)	(cdr 	(car args))]
	  [(list)	args]
	  [(append) (apply append args)]
	  
	  [(caar)	(caar	(car args))]
	  [(cadr)	(cadr	(car args))]
	  [(cdar)	(cdar	(car args))]
	  [(cddr)	(cddr	(car args))]
	  
	  [(caaar)	(caaar	(car args))]
	  [(caadr)	(caadr	(car args))]
	  [(cadar)	(cadar	(car args))]
	  [(cdaar)	(cdaar	(car args))]
	  [(caddr)	(caddr	(car args))]
	  [(cddar)	(cddar	(car args))]
	  [(cdadr)	(cdadr	(car args))]
	  [(cdddr)	(cdddr	(car args))]
	  [(list-tail) 	(apply list-tail args)]
	  [(null?)		(null? 		(car args))]
	  [(eq?)		(eq?		(car args) (cadr args))]
	  [(eqv?) 		(apply eqv? args)]
	  [(equal?)		(equal?		(car args) (cadr args))]
	  [(atom?)		(atom? 		(car args))]
	  [(list?)		(list?		(car args))]
	  [(pair?)		(pair?		(car args))]
	  [(procedure?) (proc-val?  (car args))]
	  [(vector?) 	(vector? 	(car args))]
	  [(number?) 	(number? 	(car args))]
	  [(symbol?) 	(symbol? 	(car args))]
	  
	  [(assq)	(assq	(car args) (cadr args))]
	  [(length)	(length (car args))]
	  [(vector)	(apply vector args)]
	  [(make-vector) 
			(if (null? (cdr args))
				(make-vector (car args))
				(make-vector (car args) (cadr args)))]
	  [(vector-ref) (vector-ref (car args) (cadr args))]
	  
	  [(list->vector)	(list->vector (car args))]
	  [(vector->list)	(vector->list (car args))]
	  
	  [(set-car!)		(apply set-car! args)]
	  [(set-cdr!)		(set-cdr!		(car args) (cadr args))]
	  [(vector-set!)	(apply vector-set!	args)]
	  [(quotient) (apply quotient args)]
	  [(display)	(apply display args)]
	  [(newline)	(newline)]
	  [(quote) 		(apply list args)]
	  
	  [(map) 
		(map-mine (car args) (cadr args))]
      [(apply) (apply-proc (car args) (parse-for-apply (cdr args)))]
      [(member) (apply member args)]
		[else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-op)
		]
	)
))

(define map-mine 
	(lambda (proc args) 
		(if (null? args)
			'()
			(cons (apply-proc proc (list(car args))) (map-mine proc (cdr args)))
		)
	))

(define parse-for-apply 
	(lambda (args)
		(if (null? (cdr args))
			(car args)
			(cons (car args) (parse-for-apply (cdr args)))
		)
	))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))