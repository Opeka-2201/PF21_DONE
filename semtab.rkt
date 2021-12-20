;; Semantic tableau implementation by
;; DELPORTE Guillaume - s191981
;; FIRRINCIELI Maxime - s190792
;; LOUIS Arthur       - s191230

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fonctions auxiliaires ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (atom? x)
        (and (not (null? x))
              (not (pair? x))))


;; pour une liste ls representant une formule, isDevelopped renvoie #t si ls ne 
;; contient des variables seules avec un not ou un ~
(define (isDevelopped? ls)
        (if (null? ls) 
          #t
          (let* ((head (car ls)) (rest (cdr ls)))
            (cond
              ((or (not (list? head)) (and (eq? (car head) 'NOT) (not (list? (cadar ls)))) (and (eq? (car head) '~) (not (list? (cadar ls))))) (isDevelopped? rest))
              (else #f)))))


;; pour une liste ls et un element x, is-in-list? renvoie #t si x se trouve dans ls
;; et #f sinon
(define (is-in-list? ls x)
        (cond 
          ((null? ls) #f)
          ((not (list? ls)) (is-in-list? (list ls) x))
          ((equal? (car ls) x) #t)
          (else (is-in-list? (cdr ls) x))))


;; pour une liste ls, remove-duplicates renvoie une liste contenant les memes elements 
;; en retirant les doublons
(define (remove-duplicates ls)
        (foldr (lambda (x y) (cons x (filter (lambda (z) (not (equal? x z))) y))) empty ls))


;; pour une liste ls representant une formule propositionnelle, not-list permet
;; de faire la negation de ls, comme si on rajoutait un NOT a l'avant 
(define (not-list ls)
        (if (null? ls)
          ls
          (let* ((head (car ls)) (rest (cdr ls)))
            (cond
              ((atom? head) (cons (append (list 'NOT) (list head)) (not-list rest)))
              (else (cons (append (list 'NOT)  (list head)) (not-list rest)))))))


;; pour liste args representant les arguments du OR et rest le reste de la liste
;; de formules du semtab,  ORing remplace le OR a multiple variables par une expression
;; valable dans la logique propositionnelle (application de l'algorithme des tableaux semantiques)
(define (ORing args rest)
        (if (null? args) args
        (cons (semtab (cons (car args) rest)) (semtab (ORing (cdr args) rest)))))


;; pour une liste args representant les arguments du AND et rest le reste de la liste
;; de formules du semtab,  ANDing remplace le AND a multiple variable par une expression
;; valable dans la logique propositionnelle (application de l'algorithme des tableaux semantiques)
(define (ANDing args rest)
        (if (null? args) args
        (semtab (append args rest))))  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Implementation de semtab + extension ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; pour une liste ls representant une liste de formules propositionnelles, 
;; semtab realise l'algorithme des tableaux semantique sur ls et renvoie
;; une liste de sous-listes (branches) du tableau semantique de ls
(define (semtab ls)
        (cond 
          ((null? ls) '())
          ((not (list? ls)) (semtab (list ls)))
          (else (let* ((head (car ls)) (rest (cdr ls)))
                  (cond
                    ((isDevelopped? ls) (remove-duplicates ls))
                    ;_______________________________
                    ;Cas de base
                    ((or (not (list? head)) (and (eq? (car head) 'NOT) (not (list? (cadar ls))))) (semtab (append rest (list head))))
                    ;_______________________________
                    ;NOT NOT
                    ((and (eq? (car head) 'NOT) (list? (cdr head)) (eq? (caadr head) 'NOT) (semtab (append rest (cdadr head)))))
                    ;_______________________________
                    ;AND
                    ((eq? (car head) 'AND) (ANDing (cdr head) rest))
                    ;NOT AND
                    ((and (eq? (car head) 'NOT) (eq? (caadr head) 'AND)) (semtab (cons (list 'OR (list 'NOT (cadadr head)) (list 'NOT (car (cddadr head)))) rest)))
                    ;_______________________________
                    ;OR
                    ((eq? (car head) 'OR) (ORing (cdr head) rest)) ;(semtab (cons (cadr head) rest)) (semtab (cons (caddr head) rest))
                    ;NOT OR
                    ((and (eq? (car head) 'NOT) (eq? (caadr head) 'OR)) (semtab (cons (list 'AND (list 'NOT (cadadr head)) (list 'NOT (car (cddadr head)))) rest)))
                    ;_______________________________
                    ;IFTHEN
                    ((eq? (car head) 'IFTHEN) (semtab (cons (list 'OR (list 'NOT  (cadr head)) (caddr head)) rest)))
                    ;NOT IFTHEN
                    ((and (eq? (car head) 'NOT) (eq? (caadr head) 'IFTHEN)) (semtab (cons (list 'AND (cadadr head) (list 'NOT (car (cddadr head)))) rest)))
                    ;_______________________________
                    ;_______________________________
                    ;EXTENSIONS
                    ;_______________________________
                    ;EQUIV/XNOR
                    ((or (eq? (car head) 'EQUIV) (eq? (car head) 'XNOR)) (semtab (cons (list 'OR (list 'AND (cadr head) (caddr head)) (list 'AND (list 'NOT (cadr head)) (list 'NOT (caddr head)))) rest)))
                    ;NOT EQUIV
                    ((and (eq? (car head) 'NOT) (eq? (caadr head) 'EQUIV)) (semtab (cons (list 'OR (list 'AND (list 'NOT (cadadr head)) (car (cddadr head))) (list (cadadr head) (list 'NOT (car (cddadr head))))) rest)))
                    ;XOR
                    ((eq? (car head) 'XOR) (semtab (cons (list 'OR (list 'AND (cadr head) (list 'NOT (caddr head))) (list 'AND (cadr head) (list 'NOT (caddr head)))) rest)))
                    ;NOT XOR
                    ((and (eq? (car head) 'NOT) (eq? (caadr head) 'XOR)) (semtab (cons (list 'XNOR  (cadadr head) (car (cddadr head))) rest)))
                    ;NOT XNOR
                    ((and (eq? (car head) 'NOT) (eq? (caadr head) 'XNOR)) (semtab (cons (list 'XOR (cadadr head) (car (cddadr head))) rest)))
                    ;_______________________________
                    (else ls))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Implementation de la bibliotheque ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; N.B : utilisation des fonctions expliquee dans le rapport

;;; satisfiable? :
;-----------------

;; dans le cadre de la fonction contradiciton-in-branch?, pour un un 
;; element e (represente la tete d'une branch ) et une liste ls 
;; (represente le reste de la branche), contr? renvoie si il y contradiction
;; dans la branche 
(define (contr? e ls)
        (if (null? ls) 
          #f
          (let* ((head (car ls)) (rest (cdr ls)))
            (cond
              ((atom? head) (contr? e rest))
              ((eq? e (cadr head)) #t)
              (else (contr? e rest))))))


;; pour une branche du tableau semantique ls, contradiction-in-branch? renvoie
;; #t si il y a une contradiction dans la branche (une variable et son complement 
;; dans la meme branche) en utilisant la fonction contr? pour tester chaque element
;; de la branche un a un
(define (contradiction-in-branch? ls)
        (if (null? ls)
          #f
          (if (not (isDevelopped? ls))
            (or (contradiction-in-branch? (car ls)) (contradiction-in-branch? (cdr ls)))
            (let* ((head (car ls)) (rest (cdr ls)))
              (cond
                ((atom? head) (or (contr? head (cdr ls)) (contradiction-in-branch? rest)))
                (else (or (contr? (cadr head) (semtab (not-list (cdr ls)))) (contradiction-in-branch? rest))))))))


;; pour une liste de formules ls, satisfiable? renvoie #t si le tableau semantique
;; contient au moins une branche ouverte (sans contradictions) en passant sur 
;; chaque branche du tableau semantique a l'aide de la fonction contradiction-in-branch?
(define (satisfiable? ls)
        (let ((smt (semtab ls)))
                (letrec ((loop (lambda (h)
                                (cond
                                  ((null? h) #f)
                                  ((isDevelopped? h) (not (contradiction-in-branch? h)))
                                  (else (or (loop (car h)) (loop (cdr h))))))))
                  (loop smt))))


;;; tautology? :
;---------------

;; pour une liste de formules ls, tautology? renvoie #t si la liste de formules est
;; toujours vraie et #f sinon en utilisant la fonction satisfiable? sur la negation
;; de ls
(define (tautology? ls)
        (cond
          ((null? ls) #t)
          ((not (list? ls)) (tautology? (list ls)))
          (else (not (satisfiable? (not-list ls))))))


;;; contradiction? :
;-------------------

;; pour une liste de formules ls, contradiction? renvoie #t si la liste de formules
;; est toujours fausse et #f sinon en prenant l'oppose de la fonction satisfiable? 
;; de ls
(define (contradiction? ls)
        (cond
          ((null? ls) #f)
          ((not (list? ls)) (contradiction? (list ls)))
          (else (not (satisfiable? ls)))))


;;; models :
;-----------

;; pour une branche ls, var-in-branch retourne une liste des variables contenues
;; dans la branche (different de var-in-list car on fait attention aux NOT et ~)
(define (var-in-branch ls)
        (cond
          ((null? ls) ls)
          ((not (isDevelopped? ls)) (append (var-in-branch (car ls)) (var-in-branch (cdr ls))))
          ((atom? (car ls)) (append (list (car ls)) (var-in-branch (cdr ls))))
          (else (append (list (cadar ls)) (var-in-branch (cdr ls))))))


;; pour une liste ls, var-in-list retourne une liste des variables contenues dans
;; la liste
(define (var-in-list ls)
        (cond
          ((null? ls) ls)
          ((not (list? (car ls))) (var-in-list (list ls)))
          (else (remove-duplicates (append (var-in-branch (car ls)) (var-in-list (cdr ls)))))))


;; pour une branche du table semantique br et une liste var_smt contenenant les
;; variables contenues dans le tableau semantique, compute-models retourne les
;; modeles condenses de la branche (notation ~ expliquee dans le rapport)
(define (compute-models br var_smt)
        (if (null? var_smt) 
          '()
          (let* ((var_br (var-in-branch br)) (var (car var_smt)) (rest (cdr var_smt)))
            (cond
              ((not (is-in-list? var_br var)) (cons (cons '~ (list var)) (compute-models br rest)))
              (else (compute-models br rest))))))


;; pour un tableau semantique smt et une liste de variables du tableau semantique
;; var_smt, branch-open? retourne les modeles condenses (notation ~ expliquee dans le 
;; rapport) de chaque branche ouverte a l'aide de la fonction compute-models
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


;; pour une liste de formules ls, models renvoie les modeles condenses (notation ~ 
;; expliquee dans le rapport) de ls en utilisant la fonction branch-open?
(define (models ls)
        (cond
          ((not (list? ls)) (models (list ls)))
          ((not (satisfiable? ls)) (displayln "Pas de modeles disponibles, la formule n'est pas satisfaisable"))
          (else (branch-open? (semtab ls) (var-in-list (semtab ls))))))


;;; expands (extension de models) :
;----------------------------------

;; pour deux modeles de branche branch1 branch2; same-model? retourne #t si les
;; deux modeles sont les mêmes et #f sinon en verifiant simplement qu'il n'y a 
;; pas de contradiction dans la fusion des deux modeles
(define (same-model? branch1 branch2)
        (let ((branch (append branch1 branch2)))
              (if (contradiction-in-branch? branch)
                  #f
                  #t)))


;; pour un modele de branche branch et une liste de modeles rest representant le
;; reste de la liste des modeles, renvoie #t si branch est contenu dans rest et
;; #f sinon en comparant un a un les modeles de rest avec branch en utilisant
;; la fonction same-model?
(define (twice-same-model-in-branch? branch rest)
        (cond 
          ((null? rest) #f)
          (else (let ((to_compare (car rest)))
                  (if (same-model? branch to_compare)
                      #t
                      (twice-same-model-in-branch? branch (cdr rest)))))))


;; pour une liste de modeles etendus expanded, remove-dup-models renvoie la liste de
;; modeles expanded depourvue de doublons en utilisant la fonction 
;; twice-same-model-in-branch?
(define (remove-dup-models expanded)
        (cond
          ((null? expanded) '())
          (else (let* ((branch (car expanded)) (rest (cdr expanded)))
                  (if (twice-same-model-in-branch? branch rest)
                    (append '() (remove-dup-models rest))
                    (cons branch (remove-dup-models rest)))))))


;; pour un modele mod, isFullyExpanded? renvoie #t si le modele est etendu (depourvu 
;; de notations ~) et #f sinon
(define (isFullyExpanded? mod)
        (not (and (list? (car mod)) (eq? '~ (caar mod)))))


;; pour une liste de modeles condenses (notation ~ expliquee dans le rapport),
;; expands-models renvoie la liste de modeles mod etendue (depourvue de notations ~)
(define (expands-models mod)
        (cond
          ((null? mod) '())
          ((not (list? (car mod))) mod)
          ((isFullyExpanded? (car mod)) (append mod (expands-models (cdr mod))))
          (else (let* ((branch (car mod)) (rest (cdr mod)) (tilde_var (cadar branch)))
                  (append (append (expands-models (list (append (cdr branch)
                                                (list tilde_var))))
                                  (expands-models (list (append (cdr branch) 
                                                      (list (cons 'NOT 
                                                            (list tilde_var)))))))
                          (expands-models rest))))))


;; pour une liste de modeles condenses (notation ~ expliquee dans le rapport),
;; expands renvoie la liste de modeles etendue par la fonction expands-models
;; depourvue de ses doublons grace a la fonction remove-dup-models
(define (expands mod)
        (remove-dup-models (expands-models mod)))


;;; valid? : 
;-----------

;; pour une liste de modeles hyp representant une liste d'hypotheses F et les modeles de
;; la formule psi, merge renvoie la fusion de ces deux modeles
(define (merge hyp form)
        (cond
          ((null? form) '())
          (else (cons (append hyp (car form)) (merge hyp (cdr form))))))


;; pour une liste de modeles fusionnes par la fonction merge, check-model renvoie #t si
;; un des modeles fusionnes contient une contradiction (contre-exmple trouve) et #f sinon 
(define (check-model merged)
        (is-in-list? (map contradiction-in-branch? merged) #f))


;; pour une liste de modeles de l'hypothese hyps et une liste de modeles form representant 
;; formule, compare-models retourne #t si aucun modele fusionne par la fonction merge ne
;; ne contient de contradiction (aucun contre exemple) et #f sinon 
(define (compare-models hyps form)
        (cond
          ((null? hyps) #t)
          (else (and (check-model (merge (car hyps) form)) (compare-models (cdr hyps) form)))))


;; pour une liste de formules form representant la formule psi et une liste d'hypotheses
;; representant F, valid? retourne #t si psi est valide sous F en comparant les modeles des
;; deux listes avec la fonction compare-models
(define (valid? form hyps)
        (let* ((models_form (models form)) (models_hyps (models hyps)))
          (compare-models (expands models_hyps) (expands models_form))))


;;; counterexamples :
;--------------------

;; pour une liste de modeles hyps representant les hypotheses F et une liste de modeles form
;; representant la formule psi non valide sous F, compute-counter retourne la liste des contre-
;; exemples (modeles de F non contenus dans psi) grace a la fonction check-model
(define (compute-counter hyps form)
        (cond
          ((null? hyps) '())
          ((check-model (merge (car hyps) form)) (append '() (compute-counter (cdr hyps) form)))
          (else (cons (car hyps) (compute-counter (cdr hyps) form)))))


;; pour une liste de modeles hyps representant les hypotheses F et une liste de modeles form
;; representant la formule psi, counterexamples retourne la liste des contre-exemples (modeles 
;; de F non contenus dans psi) si la psi n'est pas valide sous F, et un message signifiant que 
;; psi est valide sous F sinon
(define (counterexamples form hyps)
        (cond 
          ((valid? form hyps) (displayln "Pas de contre-exemples disponibles, formule valide sous hypothese(s)"))
          (else (let* ((models_form (expands (models form))) (models_hyps (expands (models hyps))))
                  (compute-counter models_hyps models_form)))))