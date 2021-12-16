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

(define (is-in-list? list x)
        (cond 
          ((null? list) #f)
          ((equal? (car list) x) #t)
          (else (is-in-list? (cdr list) x))))

(define (remove-duplicates ls)
        (foldr (lambda (x y) (cons x (filter (lambda (z) (not (equal? x z))) y))) empty ls))
              
(define (semtab ls)
        (if (null? ls) ls
            (let* ((head (car ls)) (rest (cdr ls)))
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
                    (else ls)))))

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
        (if (null? ls) 
          #t
          (not (satisfiable? (not-list ls)))))

(define (contradiction? ls)
        (if (null? ls)
          #f
          (not (satisfiable? ls))))

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
              ((not (isDevelopped? branch)) (cons (branch-open? branch var_smt) (branch-open? next var_smt)))
              ((contradiction-in-branch? branch) (branch-open? next var_smt))
              (else (let ((computed (compute-models branch var_smt))) 
                      (cond 
                        ((null? computed) (cons branch (branch-open? next var_smt)))
                        (else (cons (append computed branch) (branch-open? next var_smt)))))))))))

(define (models ls)
        (cond
          ((not (satisfiable? ls)) (displayln "Pas de modèles disponibles, la formule n'est pas satisfaisable"))
          (else (branch-open? (semtab ls) (var-in-list (semtab ls))))))

(define (valid? F phi)
        (cond 
          ((null? F) (not (satisfiable? (not-list phi))))
          (else (not (satisfiable? (list (append '(AND) (cons F (not-list phi)))))))))

(define (compute-counter merged)
        (if (contradiction-in-branch? merged)
          merged
          '/))

(define (expand-models ls F)
        (cond 
          ((null? ls) '())
          ((not (list? (car ls))) (cons (compute-counter (append ls F)) (expand-models (cdr ls) F))) ; branch just contains one model
          (else (let* ((branch (car ls)) (next (cdr ls)))
                        (cond 
                          ((null? branch) '())
                          ((not (list? (car branch))) (cons (compute-counter (append branch F)) (expand-models next F))) ; branch just contains one model
                          (else (let ((var (cadar branch)))
                            (cons (expand-models (append (cdr branch) (list var)) F) ; model where var is true
                                  (expand-models (cons (cdr branch) (append '(NOT) (list var))) F))))))))) ; model where var is false

(define (counterexamples F phi)
        (cond
          ((valid? F phi) (displayln "Pas de contre-exemples disponibles, f est valide sous F"))
          ((and (list? F) (= 2 (length F)) (eq? (car F) 'NOT)) (expand-models (models phi) (list F))) ; slmt NOT
          ((list? F) (expand-models (models phi) F))
          (else (expand-models (models phi) (list F)))))