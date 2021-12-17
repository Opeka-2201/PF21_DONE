;; Semantic tableau implementation by
;; DELPORTE Guillaume - s191981
;; FIRRINCIELI Maxime - s190792
;; LOUIS Arthur       - s191230

#lang racket

(define (atom? x)
        (and (not (null? x))
              (not (pair? x))))

(define (isDevelopped? ls)
        (if (null? ls) 
          #t
          (let* ((head (car ls)) (rest (cdr ls)))
            (cond
              ((or (not (list? head)) (and (eq? (car head) 'NOT) (not (list? (cadar ls)))) (and (eq? (car head) '~) (not (list? (cadar ls))))) (isDevelopped? rest))
              (else #f)))))

(define (is-in-list? ls x)
        (cond 
          ((null? ls) #f)
          ((not (list? ls)) (is-in-list? (list ls) x))
          ((equal? (car ls) x) #t)
          (else (is-in-list? (cdr ls) x))))

(define (remove-duplicates ls)
        (foldr (lambda (x y) (cons x (filter (lambda (z) (not (equal? x z))) y))) empty ls))
              
(define (semtab ls)
        (cond 
          ((null? ls) '())
          ((not (list? ls)) (semtab (list ls)))
          (else (let* ((head (car ls)) (rest (cdr ls)))
                  (cond
                    ((isDevelopped? ls) ls)
                    ;_______________________________
                    ;Cas de base
                    ((or (not (list? head)) (and (eq? (car head) 'NOT) (not (list? (cadar ls))))) (semtab (append rest (list head))))
                    ;_______________________________
                    ;NOT NOT
                    ((and (eq? (car head) 'NOT) (list? (cdr head)) (eq? (caadr head) 'NOT) (append rest (semtab (cdadr head)))))
                    ;_______________________________
                    ;AND
                    ((eq? (car head) 'AND) (semtab (append (list (cadr head) (caddr head)) rest)))
                    ;NOT AND
                    ((and (eq? (car head) 'NOT) (eq? (caadr head) 'AND)) (semtab (cons (list 'OR (list 'NOT (cadadr head)) (list 'NOT (car (cddadr head)))) rest)))
                    ;_______________________________
                    ;OR
                    ((eq? (car head) 'OR) (list (semtab (cons (cadr head) rest)) (semtab (cons (caddr head) rest))))
                    ;NOT OR
                    ((and (eq? (car head) 'NOT) (eq? (caadr head) 'OR)) (semtab (cons (list 'AND (list 'NOT (cadadr head)) (list 'NOT (car (cddadr head)))) rest)))
                    ;_______________________________
                    ;IFTHEN
                    ((eq? (car head) 'IFTHEN) (semtab (cons (list 'OR (list 'NOT  (cadr head)) (caddr head)) rest)))
                    ;NOT IFTHEN
                    ((and (eq? (car head) 'NOT) (eq? (caadr head) 'IFTHEN)) (semtab (cons (list 'AND (cadadr head) (list 'NOT (car (cddadr head)))) rest)))
                    ;_______________________________
                    (else ls))))))

(define (not-list ls)
        (if (null? ls)
          ls
          (let* ((head (car ls)) (rest (cdr ls)))
            (cond
              ((atom? head) (cons (append (list 'NOT) (list head)) (not-list rest)))
              (else (cons (append (list 'NOT)  (list head)) (not-list rest)))))))

(define (contr e ls)
        (if (null? ls) 
          #f
          (let* ((head (car ls)) (rest (cdr ls)))
            (cond
              ((atom? head) (contr e rest))
              ((eq? e (cadr head)) #t)
              (else (contr e rest))))))

(define (contradiction-in-branch? ls)
        (if (null? ls)
          #f
          (if (not (isDevelopped? ls))
            (or (contradiction-in-branch? (car ls)) (contradiction-in-branch? (cdr ls)))
            (let* ((head (car ls)) (rest (cdr ls)))
              (cond
                ((atom? head) (or (contr head (cdr ls)) (contradiction-in-branch? rest)))
                (else (or (contr (cadr head) (semtab (not-list (cdr ls)))) (contradiction-in-branch? rest))))))))

(define (satisfiable? ls)
        (let ((smt (semtab ls)))
                (letrec ((loop (lambda (h)
                                (cond
                                  ((null? h) #f)
                                  ((isDevelopped? h) (not (contradiction-in-branch? h)))
                                  (else (or (loop (car h)) (loop (cdr h))))))))
                  (loop smt))))

(define (tautology? ls)
        (cond
          ((null? ls) #t)
          ((not (list? ls)) (tautology? (list ls)))
          (else (not (satisfiable? (not-list ls))))))

(define (contradiction? ls)
        (cond
          ((null? ls) #f)
          ((not (list? ls)) (contradiction? (list ls)))
          (else (not (satisfiable? ls)))))

(define (var-in-branch ls)
        (cond
          ((null? ls) ls)
          ((not (isDevelopped? ls)) (append (var-in-branch (car ls)) (var-in-branch (cdr ls))))
          ((atom? (car ls)) (append (list (car ls)) (var-in-branch (cdr ls))))
          (else (append (list (cadar ls)) (var-in-branch (cdr ls))))))

(define (var-in-list ls)
        (cond
          ((null? ls) ls)
          ((not (list? (car ls))) (var-in-list (list ls)))
          (else (remove-duplicates (append (var-in-branch (car ls)) (var-in-list (cdr ls)))))))

(define (compute-models br var_smt)
        (if (null? var_smt) 
          '()
          (let* ((var_br (var-in-branch br)) (var (car var_smt)) (rest (cdr var_smt)))
            (cond
              ((not (is-in-list? var_br var)) (cons (cons '~ (list var)) (compute-models br rest)))
              (else (compute-models br rest))))))

(define (branch-open? smt var_smt)
        (cond
          ((null? smt) '())
          ((not (list? (car smt))) (branch-open? (list smt) var_smt))
          (else (let* ((branch (car smt)) (next (cdr smt)))
            (cond
              ((not (isDevelopped? branch)) (append (branch-open? branch var_smt) (branch-open? next var_smt)))
              ((contradiction-in-branch? branch) (branch-open? next var_smt))
              (else (let ((computed (compute-models branch var_smt))) 
                      (cond 
                        ((null? computed) (cons branch (branch-open? next var_smt)))
                        (else (cons (append computed branch) (branch-open? next var_smt)))))))))))

(define (models ls)
        (cond
          ((not (list? ls)) (models (list ls)))
          ((not (satisfiable? ls)) (displayln "Pas de modèles disponibles, la formule n'est pas satisfaisable"))
          (else (branch-open? (semtab ls) (var-in-list (semtab ls))))))

(define (isFullyExpanded? mod)
        (not (and (list? (car mod)) (eq? '~ (caar mod)))))

(define (expand mod)
        (cond
          ((null? mod) '())
          ((not (list? (car mod))) mod)
          ((isFullyExpanded? (car mod)) mod)
          (else (let* ((branch (car mod)) (rest (cdr mod)) (tilde_var (cadar branch)))
                  (append (append (expand (list (append (cdr branch)
                                                (list tilde_var))))
                                (expand (list (append (cdr branch) 
                                                      (list (cons 'NOT 
                                                            (list tilde_var)))))))
                          (expand rest))))))

(define (check-model merged)
        (is-in-list? (map contradiction-in-branch? merged) #f))

(define (merge hyp form)
        (cond
          ((null? form) '())
          (else (cons (append hyp (car form)) (merge hyp (cdr form))))))

(define (compare-models hyps form)
        (cond
          ((null? hyps) #t)
          (else (and (check-model (merge (car hyps) form)) (compare-models (cdr hyps) form)))))

(define (valid? form hyps)
        (let* ((models_form (models form)) (models_hyps (models hyps)))
          (compare-models (expand models_hyps) (expand models_form))))

(define (compute-counter hyps form)
        (cond
          ((null? hyps) '())
          ((check-model (merge (car hyps) form)) (append '() (compute-counter (cdr hyps) form)))
          (else (cons (car hyps) (compute-counter (cdr hyps) form)))))

(define (counterexamples form hyps)
        (cond 
          ((valid? form hyps) (displayln "Pas de contre-exemples disponibles, formule valide sous hypothèse(s)"))
          (else (let* ((models_form (expand (models form))) (models_hyps (expand (models hyps))))
                  (compute-counter models_hyps models_form)))))

(define test_form1 '((OR a (AND b (NOT c)))))
(define test_hyps1 '((AND (NOT a) (OR b c))))

(display "\nFormule : ")
test_form1
(display "\nHypothèses : ")
test_hyps1
(display "\nModèles de la formule : ")
(expand (models test_form1))
(display "\nModèles des hypothèses : ")
(expand (models test_hyps1))
(display "\nFormule valide sous hypothèses : ")
(valid? test_form1 test_hyps1)
(display "\nContre-exemples : ")
(counterexamples test_form1 test_hyps1)
(displayln "")

(define test_form2 '((OR a (AND b (NOT c)))))
(define test_hyps2 '((AND a (OR b c))))

(display "\nFormule : ")
test_form2
(display "\nHypothèses : ")
test_hyps2
(display "\nModèles de la formule : ")
(expand (models test_form2))
(display "\nModèles des hypothèses : ")
(expand (models test_hyps2))
(display "\nFormule valide sous hypothèses : ")
(valid? test_form2 test_hyps2)
(display "\nContre-exemples : ")
(counterexamples test_form2 test_hyps2)
(displayln "")