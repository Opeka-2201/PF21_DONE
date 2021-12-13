;; Semantic tableau implementation by
;; DELPORTE Guillaume - s191981
;; FIRRINCIELI Maxime - s190792
;; LOUIS Arthur       - s191230

(define isDevelopped? (lambda (ls)
                            (if (null? ls) #t
                     (let* ((head (car ls))
                            (rest (cdr ls)))
                   (cond
                     ((or (not (list? head)) (and (eq? (car head) 'NOT) (not (list? (cadar ls))))) (isDevelopped? rest))
                     (else #f))))))

(define (satisfiable? ls)
  )

(define semtab (lambda (ls)
                 (if (null? ls) ls
                     (let* ((head (car ls))
                            (rest (cdr ls)))
                   (cond
                     ((isDevelopped? ls) ls)
                     ;_______________________________
                     ;Cas de base
                     ((or (not (list? head)) (and (eq? (car head) 'NOT) (not (list? (cadar ls))))) (semtab (append rest (list head))))
                     ;_______________________________
                     ;NOT NOT
                     ((and (eq? (car head) 'NOT) (list? (cdr head)) (eq? (caadr head) 'NOT) (semtab (cdadr head))))
                     ;_______________________________
                     ;AND
                     ((eq? (car head) 'AND) (semtab (append (list (cadr head) (caddr head)) rest)))
                     ;NOT AND
                     ((and (eq? (car head) 'NOT) (eq? (caadr head) 'AND)) (semtab (cons (list 'OR (list 'NOT (cadadr head)) (list 'NOT (car (cddadr head)))) rest)))
                     ;_______________________________
                     ;OR
                     ((eq? (car head) 'OR) (list (semtab (cons (cadr head) rest)) (semtab (cons (caddr head) rest))))
                     ;NOT OR
                     ((and (eq? (car head) 'NOT) (eq? (caadr head) 'OR)) (semtab (cons (list 'AND (cons 'NOT (cadadr head)) (list 'NOT (car (cddadr head)))) rest)))
                     ;_______________________________
                     ;IFTHEN
                     ((eq? (car head) 'IFTHEN) (semtab (cons (list 'OR (list 'NOT  (cadr head)) (caddr head)) rest)))
                     ;NOT IFTHEN
                     ((and (eq? (car head) 'NOT) (eq? (caadr head) 'IFTHEN)) (semtab (cons (list 'AND (cadadr head) (list 'NOT (car (cddadr head)))) rest)))
                     ;_______________________________
                     (else (display "Erreur: cas non traité.")))))))

;(require racket/trace)
;(trace semtab)

(define foo '((IFTHEN p (IFTHEN q r)) (NOT (IFTHEN (IFTHEN p q) r))))
(define foot '((IFTHEN p (IFTHEN q r))))
(define test '((OR (OR p q) (NOT s))))
(define test1 '((NOT (NOT (NOT (NOT (NOT (NOT p))))))))
(define test2 '(p (AND q (OR p q)) (IFTHEN r (AND s q))))
(define test3 '((OR p q) b c d e))
(define test4 '(p (NOT (AND q p))))
(define test5 '(r s (OR p q)))
(define rep (semtab foo))