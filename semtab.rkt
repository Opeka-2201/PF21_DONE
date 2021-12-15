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
              ((or (not (list? head)) (and (eq? (car head) 'NOT) (not (list? (cadar ls))))) (isDevelopped? rest))
              (else #f)))))

(define (remove-duplicates loa)
        (foldr (lambda (x y) (cons x (filter (lambda (z) (not (equal? x z))) y))) empty loa))
              
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

(define (valid? phi F)
        (cond 
          ((null? F) #f)
          (else (not (satisfiable? (append (not-list F) (list phi)))))))

(define (var-in-branch ls)
        (cond
          ((null? ls) ls)
          ((atom? (car ls)) (append (list (car ls)) (var-in-branch (cdr ls))))
          (else (append (list (cadar ls)) (var-in-branch (cdr ls))))))

(define (var-in-list ls)
        (cond
          ((null? ls) ls)
          (else (remove-duplicates (append (var-in-branch (car ls)) (var-in-list (cdr ls)))))))

(define (compute-models br) br)

(define (branch-open? smt)
        (if (null? smt) 
          '()
          (let)
        (cond
          ((not (isDevelopped? (car smt))) (cons (branch-open? (car smt)) (branch-open? (cdr smt))))
          ((contradiction-in-branch? (car smt)) (branch-open? (cdr smt)))
          (else (cons (compute-models (car smt)) (branch-open? (cdr smt)))))))

(define (models ls)
        (cond
          ((not (satisfiable? ls)) (displayln "Pas de modèles disponibles, la formule n'est pas satisfaisable"))
          (else (displayln (branch-open? (semtab ls))))))

(define (counterexamples ls) ls)

(require racket/trace)
; (trace semtab)
; (trace satisfiable?)
; (trace valid?)
; (trace contradiction?)
; (trace tautology?)
; (trace contradiction-in-branch?)
; (trace contr)
; (trace not-list)
; (trace isDevelopped?)
; (trace atom?)
; (trace var-in-list)
(trace branch-open?)

(models '((OR a (OR b c))))