;======================================================
;                                              COMPUTING DEFEAT STATUSES

(in-package "OSCAR")

#| This fixes COMPUTE-STATUS-ASSIGNMENTS. |#

(proclaim '(special *use-reductio* *assignment-tree* *altered-links* *tree-trace*
                     *tree-number* *triangle-number* *assignment-trace* *discards*
                     *creations* *affected-nodes* *potential-supportees*
                     *potential-link-supportees* *potential-defeatees* *potential-link-defeatees*))
                     
(defvar *assignment-trace* nil)
(defvar *tree-trace* nil)
(defvar *discards* nil)
(defvar *creations* nil)

(defun print-assignment-tree (x stream depth)
    (declare (ignore depth))
    (princ "#<assignment-tree " stream) (princ (tree-number x) stream) (princ ">" stream))

(defstruct (assignment-tree (:print-function print-assignment-tree)
                                                     (:conc-name nil))
    (tree-number 1)
    (parent-tree nil)
    (node-UDs nil)
    (node-MPUDs nil)
    (link-UDs nil)
    (link-MPUDs nil)
    (triangle-sets nil))

(defun print-triangle-set (x stream depth)
    (declare (ignore depth))
    (princ "#<triangle-set " stream) (princ (triangle-number x) stream) (princ ">" stream))

(defstruct (triangle-set (:print-function print-triangle-set)
                                         (:conc-name nil))
    (triangle-number 0)
    (triangle-domain nil)
    (assignment-trees nil))

#| The assignment-tree with number n: |#
(defunction assignment-tree (n)
    (catch 'number
        (find-tree n *assignment-tree*)))

(defunction find-tree (n assignment-tree)
    (cond ((eql (tree-number assignment-tree) n)
                 (throw 'number assignment-tree))
                (t (dolist (triangle (triangle-sets assignment-tree))
                       (dolist (tree (assignment-trees triangle))
                           (find-tree n tree))))))

#| The triangle-set with number n: |#
(defunction triangle-set (n)
    (catch 'number
        (find-triangle n *assignment-tree*)))

(defunction find-triangle (n assignment-tree)
    (dolist (triangle (triangle-sets assignment-tree))
        (cond ((eql (triangle-number triangle) n)
                     (throw 'number triangle))
                    (t (dolist (tree (assignment-trees triangle))
                           (find-triangle n tree))))))

(defun display-assignment-tree (&optional tree (depth 0) stream)
    (when (null tree) (setf tree *assignment-tree*))
    (indent depth stream) (princ "assignment-tree " stream) (princ (tree-number tree) stream)
    (princ ":" stream) (terpri stream)
    (print-list (node-UDs tree) 4 (+ 1 depth) stream) (terpri stream)
    (dolist (triangle (triangle-sets tree))
        (display-triangle triangle (+ 1 depth) stream)))

#|
(defun display-assignment-tree (&optional tree (depth 0) stream)
    (when (null tree) (setf tree *assignment-tree*))
    (indent depth stream) (princ "assignment-tree " stream) (princ (tree-number tree) stream)
    (princ ":" stream) (terpri stream)
    (print-list 
      (mapcar #'(lambda (x y) (list (car x) (cdr x) (cdr y)))
                     (node-UDs tree) (node-MPUDs tree))
     ; (node-UDs tree)
      5 (+ 1 depth) stream) (terpri stream)
    (dolist (triangle (triangle-sets tree))
        (display-triangle triangle (+ 1 depth) stream)))
|#

(defun display-triangle (triangle depth stream)
    (indent depth stream) (princ "triangle " stream) (princ (triangle-number triangle) stream)
    (princ ":" stream) (terpri stream)
    (print-list (triangle-domain triangle) 5 (1+ depth) stream) (terpri stream)
    (dolist (tree (assignment-trees triangle))
        (display-assignment-tree tree (+ 3 depth) stream)))

#| This computes the number of branches in an assignment-tree. |#
(defunction size-of-tree (tree)
    (If (null (triangle-sets tree)) 1
    (apply #'+ (mapcar #'size-of-triangle (triangle-sets tree)))))

(defunction size-of-triangle (triangle)
    (apply #'+ (mapcar #'size-of-tree (assignment-trees triangle))))

#| This toggles tree tracing on and off. |#
(defunction tree-trace ()
    (cond ((not (boundp '*tree-trace*)) (setf *tree-trace* t))
                (t
                  (if *tree-trace* (setf *tree-trace* nil) (setf *tree-trace* t)))))

#| This computes minimal triangle-sets.  This makes the generating link the
first member of the triangle-domain. |#

(defunction compute-triangle-domains (tree)
   ; (setf *tree* tree)
    (let ((Y nil))
       (dolist (as (node-UDs tree))
           (dolist (L (consequent-links (car as)))
               (when (and (not (member L Y))
                                     (not (tree-link-UD L tree))
                                     (every #'(lambda (b)
                                                       (or (eq b (car as))
                                                             (tree-node-UD b tree)))
                                                  (support-link-basis L)))
                    (push L Y))))
       (when Y
            (let* ((triangle-domains nil))
               (dolist (L Y)
                   (let* ((triangle (inference/defeat-ancestors (list L) tree)))
                      (when (mem L triangle)
                           (dolist (td triangle-domains)
                               (when (mem L td)
                                    (pull td triangle-domains)))
                           (when (not (some
                                                 #'(lambda (td) (mem (mem1 td) triangle))
                                                 triangle-domains))
                                (push (cons L (remove L triangle)) triangle-domains)))))
               triangle-domains))))

#| node-UDs is a list of either dotted pairs (node . val) or (node val . cycle). |#
(defunction tree-node-UD* (node tree)
    (let ((assoc (assoc node (node-UDs tree))))
      (when assoc
           (cond ((numberp (cdr assoc)) assoc)
                     (t
                       (let ((cycle (cddr assoc)))
                         (cond ((not (eql cycle *cycle*))
                                     (cons node
                                               (cons
                                                 (adjust-for-decay (cadr assoc) (expt *temporal-decay* (- *cycle* cycle)))
                                                 *cycle*)))
                                   (t assoc))))))))

(defunction tree-node-MPUD* (node tree)
    (let ((assoc (assoc node (node-MPUDs tree))))
      (when assoc
           (cond ((numberp (cdr assoc)) assoc)
                     (t
                       (let ((cycle (cddr assoc)))
                         (cond ((not (eql cycle *cycle*))
                                     (cons node
                                               (cons
                                                 (adjust-for-decay (cadr assoc) (expt *temporal-decay* (- *cycle* cycle)))
                                                 *cycle*)))
                                   (t assoc))))))))

(defunction tree-link-UD* (link tree)
    (let ((assoc (assoc link (link-UDs tree))))
      (when assoc
           (cond ((numberp (cdr assoc)) assoc)
                     (t
                       (let ((cycle (cddr assoc)))
                         (cond ((not (eql cycle *cycle*))
                                     (cons link
                                               (cons
                                                 (adjust-for-decay (cadr assoc) (expt *temporal-decay* (- *cycle* cycle)))
                                                 *cycle*)))
                                   (t assoc))))))))

(defunction tree-link-MPUD* (link tree)
    (let ((assoc (assoc link (link-MPUDs tree))))
      (when assoc
           (cond ((numberp (cdr assoc)) assoc)
                     (t
                       (let ((cycle (cddr assoc)))
                         (cond ((not (eql cycle *cycle*))
                                     (cons link
                                               (cons
                                                 (adjust-for-decay (cadr assoc) (expt *temporal-decay* (- *cycle* cycle)))
                                                 *cycle*)))
                                   (t assoc))))))))

#| If node has an assigned status in assignment-tree or one of its ancestors,
this returns (node.status). |#
(defunction tree-node-UD (node assignment-tree)
    (if assignment-tree
       (or (tree-node-UD* node assignment-tree)
             (tree-node-UD node (parent-tree assignment-tree)))))

#| If node has an assigned status in assignment-tree or one of its ancestors,
this returns (node.status). |#
(defunction tree-node-MPUD (node assignment-tree)
    (if assignment-tree
       (or (tree-node-MPUD* node assignment-tree)
             (tree-node-MPUD node (parent-tree assignment-tree)))))

#| If link has an assigned status in assignment-tree or one of its ancestors,
this returns (link.status). |#
(defunction tree-link-UD (link assignment-tree)
    (if assignment-tree
       (or (tree-link-UD* link assignment-tree)
             (tree-link-UD link (parent-tree assignment-tree)))))

#| If link has an assigned status in assignment-tree or one of its ancestors,
this returns (link.status). |#
(defunction tree-link-MPUD (link assignment-tree)
    (if assignment-tree
       (or (tree-link-MPUD* link assignment-tree)
             (tree-link-MPUD link (parent-tree assignment-tree)))))

;(defunction assoc-value (assoc)
;    (when assoc
;         (cond ((listp (cdr assoc)) (cadr assoc))
;                   (t (cdr assoc)))))

(defunction assoc-value (assoc)
    (when assoc
         (cond ((listp (cdr assoc))
                     (let ((cycle (cddr assoc)))
                       (when (not (eql cycle *cycle*))
                            (setf (cdr assoc)
                                     (cons
                                       (adjust-for-decay (cadr assoc) (expt *temporal-decay* (- *cycle* cycle)))
                                       *cycle*))))
                     (cadr assoc))
                   (t (cdr assoc)))))

(defunction make-node-assoc (node value)
    (cond ((temporal-node node) (cons node (cons value *cycle*)))
              (t (cons node value))))

(defunction make-link-assoc (link value)
    (cond ((temporal-link link) (cons link (cons value *cycle*)))
              (t (cons link value))))

#| X is a list of support-links.  This finds the list of support-links that are inference/defeat-ancestors
and are not assigned values by tree or assignment. |#
(defunction inference/defeat-ancestors (X tree &optional ancestors)
    (let ((new-ancestors nil))
       (dolist (L X)
           (dolist (d (support-link-defeaters L))
               (dolist (L* (support-links d))
                    (when (and (not (member L* new-ancestors))
                                          (not (member L* ancestors))
                                          (not (tree-link-UD L* tree)))
                         (push L* new-ancestors))))
           (dolist (b (support-link-basis L))
               (dolist (L* (support-links b))
                    (when (and (not (member L* new-ancestors))
                                          (not (member L* ancestors))
                                          (not (tree-link-UD L* tree)))
                         (push L* new-ancestors)))))
       (cond ((null new-ancestors) ancestors)
                   (t
                     (inference/defeat-ancestors
                       new-ancestors tree (append new-ancestors ancestors))))))

;; ----------------------------------------------------------------------

(defunction compute-assignment-tree (&optional assignment parent-tree (indent-level 0))
    (when (null assignment)
         (setf *tree-number* 0)
         (setf *triangle-number* 0)
         (dolist (node *inference-graph*)
             (setf (undefeated-degree-of-support node) nil))
         (dolist (L *support-links*)
             (setf (defeating-assignment-trees L) nil))
         (let* ((initial-nodes
                     (subset
                       #'(lambda (N)
                             (or (null (support-links N))
                                   (some
                                     #'(lambda (L) (null (support-link-basis L)))
                                     (support-links N))))
                       *inference-graph*))
                   (link-assignment nil))
           (dolist (N initial-nodes)
               (dolist (L (support-links N))
                   (when (null (support-link-basis L))
                        (push (cons L (maximal-degree-of-support N)) link-assignment))))
           (let ((node-assignment
                     (mapcar #'(lambda (N) (cons N (maximal-degree-of-support N)))
                                    initial-nodes)))
             (multiple-value-bind
                  (link-UDs link-MPUDs node-UDs node-MPUDs)
                  (dual-assignment-closure
                    link-assignment link-assignment node-assignment node-assignment nil nil nil)
                  (setf assignment (vector link-UDs link-MPUDs node-UDs node-MPUDs))))))
    (when *tree-trace*
         (indent indent-level) (princ "assignment-tree ")
         (princ (1+ *tree-number*))
         (princ ":  ") (terpri) (print-list (mem2 assignment) 5 (+ 1 indent-level)) (terpri))
    (let* ((tree (make-assignment-tree
                         :tree-number (incf *tree-number*)
                         :parent-tree parent-tree
                         :node-UDs (elt assignment 2)
                         :node-MPUDs (elt assignment 3)
                         :link-UDs (elt assignment 0)
                         :link-MPUDs (elt assignment 1)))
              (triangles
                (compute-triangle-domains tree)))
      (setf (triangle-sets tree)
               (mapcar
                 #'(lambda (triangle)
                       (when *tree-trace*
                            (indent (+ 1 indent-level)) (princ "triangle ")
                            (princ (1+ *triangle-number*)) (princ ":  ") (terpri)
                            (print-list triangle 5 (+ 2 indent-level)) (terpri))
                       (compute-triangle-set triangle tree indent-level))
                 triangles))
      (dolist (assoc (elt assignment 0))
          (when (>< 0.0 (assoc-value assoc))
               (push tree (defeating-assignment-trees (car assoc)))
               (push (car assoc) *altered-links*)))
      (when *display?* (push tree *creations*))
      tree))

#| This is the closure under the rules for extending assignments of the result of adding
a new list of support-link assignments arb-UD arb-MPUD to the assignments generated by tree
and the background-assignment assignment.  arb is a vector of two a-lists, arb-UD and arb-MPUD.
The optional assignment is a vector of four a-lists -- node-UDs, node-MPUD's, link-UDs, link-MPUDs.
It is assumed that the domain of arb consists of support-links not previously assigned values.
This returns eight values -- link-UDs link-MPUDs node-UDs node-MPUDs and the list of newly 
assigned nodes and newly-assigned links, or nil if the closure is inconsistent. |#
(defunction assignment-closure
    (arb-UD arb-MPUD tree &optional link-UDs link-MPUDs node-UDs node-MPUDs)
   ; (setf au arb-UD am arb-MPUD tr tree lu link-uds lm link-mpuds nu node-uds nm node-mpuds) ; (break)
    ;; (step (assignment-closure au am tr lu lm nu nm))
    (catch 'consistency-check
       (closure-with-consistency-check
           arb-UD arb-MPUD tree nil nil link-UDs link-MPUDs node-UDs node-MPUDs nil nil nil nil)))

#| nodes is the list of newly-assigned-nodes. If D1 and D2 are not nil, only nodes in D2 and links in D1
have values computed.  This returns eight values -- link-UDs link-MPUDs node-UDs node-MPUDs and
the list of newly assigned nodes and newly-assigned links. |#
(defunction closure-with-consistency-check
    (arb-UD arb-MPUD tree D1 D2 link-UDs link-MPUDs node-UDs node-MPUDs nodes1 nodes2 links1 links2)
    (cond
      ((null arb-UD)
        (if tree
          (values
            (append (link-UDs tree) link-UDs)
            (append (link-MPUDs tree) link-MPUDs)
            (append (node-UDs tree) node-UDs)
            (append (node-MPUDs tree) node-MPUDs)
            nodes1 nodes2 links1 links2)
          (values link-UDs link-MPUDs node-UDs node-MPUDs nodes1 nodes2 links1 links2)))
      (t
        (multiple-value-bind
             (dictated-link-UDs dictated-link-MPUDs dictated-node-UDs dictated-node-MPUDs
                                           ud-nodes mpud-nodes ud-links mpud-links)
             (dictated-values arb-UD arb-MPUD tree D1 D2 link-UDs link-MPUDs node-UDs node-MPUDs)
             (closure-with-consistency-check
               dictated-link-UDs dictated-link-MPUDs tree D1 D2
               (append arb-UD link-UDs) (append arb-MPUD link-MPUDs)
               (append dictated-node-UDs node-UDs) (append dictated-node-MPUDs node-MPUDs)
               (append ud-nodes nodes1) (append mpud-nodes nodes2)
               (append ud-links links1) (append mpud-links links2))))))

#| This is the closure simultaneously of a set of link-assignments and a set of node-
assignments.  If D1 and D2 are not nil, only nodes in D2 and links in D1 have values computed.
This returns  eight values -- link-UDs link-MPUDs node-UDs node-MPUDs nodes links. |#
(defunction dual-assignment-closure
    (arb-link-UD arb-link-MPUD arb-node-UD arb-node-MPUD tree 
                        &optional D1 D2 ass-link-UD ass-link-MPUD ass-UD ass-MPUD)
   ; (setf aul arb-link-UD aml arb-link-MPUD aun arb-node-UD amn arb-node-MPUD tr tree
   ;          d1* d1 d2* d2 alu ass-link-UD alm ass-link-MPUD au ass-UD am ass-MPUD) ; (break)
    ;; (step (dual-assignment-closure aul aml aun amn tr d1* d2* alu alm au am))
    (catch 'consistency-check
        (dual-closure-with-consistency-check
          arb-link-UD arb-link-MPUD arb-node-UD arb-node-MPUD tree D1 D2
          ass-link-UD ass-link-MPUD ass-UD ass-MPUD)))

(defunction dual-closure-with-consistency-check
    (arb-link-UD arb-link-MPUD arb-node-UD arb-node-MPUD tree
                        D1 D2 link-UDs link-MPUDs node-UDs node-MPUDs)
    (multiple-value-bind
         (dictated-link-UDs dictated-link-MPUDs)
         (dictated-values-from-nodes
           arb-node-UD arb-node-MPUD tree D1 link-UDs link-MPUDs node-UDs node-MPUDs nil nil)
         (closure-with-consistency-check
           (append dictated-link-UDs arb-link-UD) (append dictated-link-MPUDs arb-link-MPUD)
           tree D1 D2 link-UDs link-MPUDs (append arb-node-UD node-UDs)
           (append arb-node-MPUD node-MPUDs) (domain arb-node-MPUD) (domain arb-node-UD)
           (domain arb-link-MPUD) (domain arb-link-UD))))

#| This returns eight values -- dictated-link-UDs dictated-link-MPUDs dictated-node-UDs 
dictated-node-MPUDs and the lists of nodes and links having newly dictated values.  If D1 and D2
are not nil, only nodes in D2 and links in D1 have values computed. |#
(defunction dictated-values (arb-UD arb-MPUD tree D1 D2 link-UD link-MPUD node-UD node-MPUD)
   ; (setf au arb-UD am arb-MPUD tr tree lu link-ud lm link-mpud nu node-ud nm node-mpud) ; (break)
    ;; (step (dictated-values au am tr nil nil lu lm nu nm))
    (multiple-value-bind
         (dictated-node-UDs dictated-node-MPUDs ud-nodes mpud-nodes)
         (dictated-values-from-support-links
           arb-UD arb-MPUD tree D2 link-UD link-MPUD node-UD node-MPUD)
         (dictated-values-from-nodes
           dictated-node-UDs dictated-node-MPUDs tree D1 link-UD
           link-MPUD node-UD node-MPUD ud-nodes mpud-nodes)))

(defunction dictated-values-from-support-links
    (arb-UD arb-MPUD tree D2 link-UD link-MPUD node-UDs node-MPUDs)
    ; (setf au arb-UD am arb-MPUD tr tree d d2 lu link-ud lm link-mpud nu node-UDs nm node-MPUDs)
    ;; (step (dictated-values-from-support-links au am tr d lu lm nu nm))
    (let ((dictated-node-UDs nil)
            (dictated-node-MPUDs nil)
            (ud-nodes nil)
            (mpud-nodes nil))
      (dolist (link (union (domain arb-UD) (domain arb-MPUD)))
          (let ((node (support-link-target link)))
            (when
                 (or (null D2) (member node D2))
                 (let ((unassigned-link-UDs nil)
                         (unassigned-link-MPUDs nil)
                         (link-UDs nil)
                         (link-MPUDs nil))
                   (dolist (L (support-links node))
                       (let ((assoc1 (link-assoc-UD L link-UD arb-UD tree))
                               (assoc2 (link-assoc-MPUD L link-MPUD arb-MPUD tree)))
                         (cond (assoc1 (push (assoc-value assoc1) link-UDs))
                                   (t (push L unassigned-link-UDs)))
                         (cond (assoc2 (push (assoc-value assoc2) link-MPUDs))
                                   (t (push L unassigned-link-MPUDs)))))
                   (let ((new-UD (maximum0 link-UDs))
                           (new-MPUD (maximum0 link-MPUDs))
                           (max-link-strength
                             (maximum0 (mapcar #'support-link-maximal-strength 
                                                                 (union unassigned-link-UDs unassigned-link-MPUDs)))))
                     (cond ((>< new-UD new-MPUD)
                                 (when (>>= new-UD max-link-strength)
                                      (let ((node-UD
                                                (assoc-value (node-assoc-UD node dictated-node-UDs node-UDs tree)))
                                              (node-MPUD
                                                (assoc-value (node-assoc-MPUD node dictated-node-MPUDs node-MPUDs tree))))
                                        (cond (node-UD
                                                    (if (or (not (>< node-UD new-UD)) (not (>< node-MPUD new-MPUD))) 
                                                      (throw 'consistency-check nil)
                                                      (progn
                                                          (push node ud-nodes)
                                                          (push node mpud-nodes))))
                                                  (t
                                                    (push (make-node-assoc node new-UD) dictated-node-UDs)
                                                    (push (make-node-assoc node new-MPUD) dictated-node-MPUDs)
                                                    (push node ud-nodes)
                                                    (push node mpud-nodes))))))
                               (t
                                 (when (>>= new-UD max-link-strength)
                                      (let ((node-UD
                                                (assoc-value (node-assoc-UD node dictated-node-UDs node-UDs tree))))
                                        (cond (node-UD
                                                    (if (not (>< node-UD new-UD))
                                                      (throw 'consistency-check nil)
                                                      (push node ud-nodes)))
                                                    (t
                                                    (push (make-node-assoc node new-UD) dictated-node-UDs)
                                                    (push node ud-nodes)))))
                                 (when (>>= new-UD max-link-strength)
                                      (let ((node-MPUD
                                                (assoc-value (node-assoc-MPUD node dictated-node-MPUDs node-MPUDs tree))))
                                        (cond (node-MPUD
                                                    (if (not (>< node-MPUD new-MPUD))
                                                      (throw 'consistency-check nil)
                                                      (push node mpud-nodes)))
                                                  (t
                                                    (push (make-node-assoc node new-MPUD) dictated-node-MPUDs)
                                                    (pushnew node mpud-nodes))))))))))))
      (values dictated-node-UDs dictated-node-MPUDs ud-nodes mpud-nodes)))

(defunction dictated-values-from-nodes
    (arb-UD arb-MPUD tree D1 link-UD link-MPUD node-UD node-MPUD ud-nodes mpud-nodes)
    ; (setf au arb-UD am arb-MPUD tr tree d d1 lu link-ud lm link-mpud nu node-ud nm node-mpud un ud-nodes mn mpud-nodes)
    ;; (step (dictated-values-from-nodes au am tr d lu lm nu nm un mn))
    (let ((dictated-link-UDs nil)
            (dictated-link-MPUDs nil)
            (ud-links nil)
            (mpud-links nil))
      (dolist (node (union (domain arb-UD) (domain arb-MPUD)))
          (let* ((UD (assoc-value (assoc node arb-UD)))
                    (MPUD (assoc-value (assoc node arb-MPUD))))
            ;; ==========================================================
            (dolist (link (consequent-links node))
                (when (or (null D1) (member link D1))
                     (let ((basis-UDs (if UD (list UD)))
                             (basis-MPUDs (if MPUD (list MPUD)))
                             (defeater-UDs nil)
                             (defeater-MPUDs nil)
                             (unassigned-basis-UDs nil)
                             (unassigned-basis-MPUDs nil)
                             (unassigned-defeater-UDs nil)
                             (unassigned-defeater-MPUDs nil)
                             (new-UD nil)
                             (new-MPUD nil))
                       (cond ((eql MPUD 0.0) (setf new-UD 0.0 new-MPUD 0.0))
                                 ((eql UD 0.0) (setf new-UD 0.0)))
                       (when new-UD
                            (let ((link-UD (assoc-value (link-assoc-UD link dictated-link-UDs link-UD tree))))
                              (cond (link-UD
                                          (if (not (>< link-UD new-UD))
                                            (throw 'consistency-check nil)
                                            (progn
                                                (pushnew link ud-links)
                                                (pushnew link mpud-links))))
                                        (t
                                          (push (make-link-assoc link new-UD) dictated-link-UDs)
                                          (pushnew link ud-links)
                                          (pushnew link mpud-links)))))
                       (when new-MPUD
                            (let ((link-MPUD (assoc-value (link-assoc-MPUD link dictated-link-MPUDs link-MPUD tree))))
                              (cond (link-MPUD
                                          (if (not (>< link-MPUD new-MPUD))
                                            (throw 'consistency-check nil)
                                            (pushnew link mpud-links)))
                                        (t
                                          (push (make-link-assoc link new-MPUD) dictated-link-MPUDs)
                                          (pushnew link mpud-links)))))
                       (when (null new-MPUD)
                            (dolist (b (support-link-basis link))
                                (when (and (null new-UD) (or (null UD) (not (eq b node))))
                                     (let ((assoc (node-assoc-UD b node-UD arb-UD tree)))
                                       (cond (assoc (push (assoc-value assoc) basis-UDs))
                                                 (t (push b unassigned-basis-UDs)))))
                                (when (or (null MPUD) (not (eq b node)))
                                     (let ((assoc (node-assoc-MPUD b node-MPUD arb-MPUD tree)))
                                       (cond (assoc (push (assoc-value assoc) basis-MPUDs))
                                                 (t (push b unassigned-basis-MPUDs))))))
                            (let* ((temp
                                        (or (eq (support-link-rule link) *temporal-projection*)
                                              (eq (support-link-rule link) *causal-implication*)
                                              (and (not (keywordp (support-link-rule link)))
                                                       (temporal? (support-link-rule link)))))
                                      (beta (if (null new-UD)
                                                  (if temp
                                                    (* (support-link-reason-strength link) (minimum0 basis-UDs))
                                                    (minimum (cons (support-link-reason-strength link)  basis-UDs)))))
                                      (beta*
                                        (if temp
                                          (* (support-link-reason-strength link) (minimum0 basis-MPUDs))
                                          (minimum (cons (support-link-reason-strength link) basis-MPUDs)))))
                              (dolist (d (support-link-defeaters link))
                                  (let ((value (assoc-value (node-assoc-UD d node-UD arb-UD tree))))
                                    (cond (value
                                                (when (or (>>= value beta*)
                                                                  (some
                                                                    #'(lambda (b)
                                                                          (>>= value (maximal-degree-of-support b)))
                                                                    unassigned-basis-MPUDs))
                                                     (setf new-MPUD 0.0) (setf new-UD 0.0) (return))
                                                (push value defeater-UDs))
                                              (t (push d unassigned-defeater-UDs)))))
                              (when (null new-UD)
                                   (dolist (d (support-link-defeaters link))
                                       (let ((value (assoc-value (node-assoc-MPUD d node-MPUD arb-MPUD tree))))
                                         (cond (value
                                                     (when (or (>>= value beta)
                                                                       (some
                                                                         #'(lambda (b)
                                                                               (>>= value (maximal-degree-of-support b)))
                                                                         unassigned-basis-MPUDs))
                                                          (setf new-UD 0.0) (return))
                                                     (push value defeater-MPUDs))
                                                   (t (push d unassigned-defeater-MPUDs))))))
                              (cond (new-UD
                                          (let ((link-UD (assoc-value (link-assoc-UD link dictated-link-UDs link-UD tree))))
                                            (cond (link-UD
                                                        (if (not (>< link-UD new-UD))
                                                          (throw 'consistency-check nil)
                                                          (progn
                                                              (pushnew link ud-links)
                                                              (pushnew link mpud-links))))
                                                      (t
                                                        (push (make-link-assoc link new-UD) dictated-link-UDs)
                                                        (pushnew link ud-links)
                                                        (pushnew link mpud-links)))))
                                        ((and
                                           (null unassigned-basis-UDs)
                                           (every #'(lambda (delta*) (<< delta* beta)) defeater-MPUDs)
                                           (every #'(lambda (d) (<< (maximal-degree-of-support d) beta))
                                                       unassigned-defeater-MPUDs))
                                          (let ((link-UD (assoc-value (link-assoc-UD link dictated-link-UDs link-UD tree))))
                                            (cond (link-UD
                                                        (if (not (>< link-UD beta))
                                                          (throw 'consistency-check nil)
                                                          (pushnew link ud-links)))
                                                      (t
                                                        (push (make-link-assoc link beta) dictated-link-UDs)
                                                        (pushnew link ud-links))))))
                            (cond (new-MPUD
                                        (let ((link-MPUD
                                                  (assoc-value (link-assoc-MPUD link dictated-link-MPUDs link-MPUD tree))))
                                          (cond (link-MPUD
                                                      (if (not (>< link-MPUD new-MPUD))
                                                        (throw 'consistency-check nil)
                                                        (pushnew link mpud-links)))
                                                    (t
                                                      (push (make-link-assoc link new-MPUD) dictated-link-MPUDs)
                                                      (pushnew link mpud-links)))))
                                      ((and
                                         (null unassigned-basis-MPUDs)
                                         (every #'(lambda (delta) (<< delta beta*)) defeater-UDs)
                                         (every #'(lambda (d) (<< (maximal-degree-of-support d) beta*))
                                                     unassigned-defeater-UDs))
                                        (let ((link-MPUD
                                                  (assoc-value (link-assoc-MPUD link dictated-link-MPUDs link-MPUD tree))))
                                          (cond (link-MPUD
                                                      (if (not (>< link-MPUD beta*))
                                                        (throw 'consistency-check nil)
                                                        (pushnew link mpud-links)))
                                                    (t
                                                      (push (make-link-assoc link beta*) dictated-link-MPUDs)
                                                      (pushnew link mpud-links)))))))))))
            ;; ==========================================================
            (dolist (link (node-defeatees node))
                (when (or (null D1) (member link D1))
                     (let ((basis-UDs nil)
                             (basis-MPUDs nil)
                             (new-UD nil)
                             (new-MPUD nil)
                             (unassigned-basis-UDs nil)
                             (unassigned-basis-MPUDs nil)
                             (unassigned-defeater-UDs nil)
                             (unassigned-defeater-MPUDs nil)
                             (UD*
                               (if (and UD
                                            (or (eq (support-link-rule link) *temporal-projection*)
                                                  (eq (support-link-rule link) *causal-implication*)
                                                  (and (not (keywordp (support-link-rule link)))
                                                           (temporal? (support-link-rule link)))))
                                 (/ UD (support-link-reason-strength link)) UD))
                             (MPUD*
                               (if (and MPUD
                                            (or (eq (support-link-rule link) *temporal-projection*)
                                                  (eq (support-link-rule link) *causal-implication*)
                                                  (and (not (keywordp (support-link-rule link)))
                                                           (temporal? (support-link-rule link)))))
                                 (/ MPUD (support-link-reason-strength link)) MPUD)))
                       (cond ((and UD (>>= UD (support-link-reason-strength link)))
                                   (setf new-MPUD 0.0) (setf new-UD 0.0))
                                 ((and MPUD (>>= MPUD (support-link-reason-strength link)))
                                   (setf new-UD 0.0))
                                 (t
                                   (dolist (b (support-link-basis link))
                                       (let ((value (assoc-value (node-assoc-MPUD b node-MPUD arb-MPUD tree))))
                                         (cond (value
                                                     (when (>>= UD* value) (setf new-MPUD 0.0 new-UD 0.0) (return))
                                                     (push value basis-MPUDs))
                                                   (t
                                                     (when (>>= UD* (maximal-degree-of-support b))
                                                          (setf new-UD 0.0 new-MPUD 0.0) (return))
                                                     (push b unassigned-basis-mpuds)))))))
                       (when (null new-UD)
                            (dolist (b (support-link-basis link))
                                (let ((value (assoc-value (node-assoc-UD b node-UD arb-UD tree))))
                                  (cond (value
                                              (when (>>= MPUD* value) (setf new-UD 0.0) (return))
                                              (push value basis-UDs))
                                            (t
                                              (when (>>= MPUD* (maximal-degree-of-support b))
                                                   (setf new-UD 0.0) (return))
                                              (push b unassigned-basis-uds))))))
                       (when (null new-MPUD)
                             (dolist (b (support-link-basis link))
                                 (let ((value (assoc-value (node-assoc-MPUD b node-MPUD arb-MPUD tree))))
                                    (cond (value
                                                  (when (>>= UD* value) (setf new-MPUD 0.0) (return))
                                                  (push value basis-MPUDs))
                                                (t
                                                  (when (>>= UD* (maximal-degree-of-support b))
                                                        (setf new-MPUD 0.0) (return))
                                                  (push b unassigned-basis-mpuds))))))
                       (cond (new-UD
                                   (let ((link-UD (assoc-value (link-assoc-UD link dictated-link-UDs link-UD tree))))
                                     (cond (link-UD
                                                 (if (not (>< link-UD new-UD))
                                                   (throw 'consistency-check nil)
                                                   (pushnew link ud-links)))
                                               (t
                                                 (push (make-link-assoc link new-UD) dictated-link-UDs)
                                                 (pushnew link ud-links)))))
                                 ((null unassigned-basis-UDs)
                                   (let ((beta
                                             (if (or (eq (support-link-rule link) *temporal-projection*)
                                                       (eq (support-link-rule link) *causal-implication*)
                                                       (and (not (keywordp (support-link-rule link)))
                                                                (temporal? (support-link-rule link))))
                                               (* (support-link-reason-strength link)  (minimum0 basis-UDs))
                                               (minimum (cons (support-link-reason-strength link)  basis-UDs)))))
                                     (when
                                          (and
                                            (every
                                              #'(lambda (d)
                                                    (let ((assoc
                                                              (node-assoc-MPUD d node-MPUD arb-MPUD tree)))
                                                      (or (null assoc) (<< (assoc-value assoc) beta)
                                                            (<< (maximal-degree-of-support d) beta))))
                                              (support-link-defeaters link))
                                            (every #'(lambda (d) (<< (maximal-degree-of-support d) beta))
                                                        unassigned-defeater-MPUDs))
                                          (let ((link-UD (assoc-value (link-assoc-UD link dictated-link-UDs link-UD tree))))
                                            (cond (link-UD
                                                        (if (not (>< link-UD beta))
                                                          (throw 'consistency-check nil)
                                                          (pushnew link ud-links)))
                                                      (t
                                                        (push (make-link-assoc link beta) dictated-link-UDs)
                                                        (pushnew link ud-links))))))))
                       (cond (new-MPUD
                                   (let ((link-MPUD
                                             (assoc-value (link-assoc-MPUD link dictated-link-MPUDs link-MPUD tree))))
                                     (cond (link-MPUD
                                                 (if (not (>< link-MPUD new-MPUD)) (throw 'consistency-check nil)))
                                               (t
                                                 (push (make-link-assoc link new-MPUD) dictated-link-MPUDs)))))
                                 ((null unassigned-basis-MPUDs)
                                   (let ((beta*
                                             (if (or (eq (support-link-rule link) *temporal-projection*)
                                                       (eq (support-link-rule link) *causal-implication*)
                                                       (and (not (keywordp (support-link-rule link)))
                                                                (temporal? (support-link-rule link))))
                                               (* (support-link-reason-strength link)  (minimum0 basis-MPUDs))
                                               (minimum (cons (support-link-reason-strength link)  basis-MPUDs)))))
                                     (when
                                          (and
                                            (every
                                              #'(lambda (d)
                                                    (or (eq d node)
                                                          (let ((assoc
                                                                    (node-assoc-UD d node-UD arb-UD tree)))
                                                            (or (null assoc) (<< (assoc-value assoc) beta*)
                                                                  (<< (maximal-degree-of-support d) beta*)))))
                                              (support-link-defeaters link))
                                            (every #'(lambda (d) (<< (maximal-degree-of-support d) beta*))
                                                        unassigned-defeater-UDs))
                                          (let ((link-MPUD
                                                    (assoc-value (link-assoc-MPUD link dictated-link-MPUDs link-MPUD tree))))
                                            (cond (link-MPUD
                                                        (if (not (>< link-MPUD beta*))
                                                          (throw 'consistency-check nil)
                                                          (pushnew link mpud-links)))
                                                      (t
                                                        (push (make-link-assoc link beta*) dictated-link-MPUDs)
                                                        (pushnew link mpud-links)))))))))))
            ;; ==========================================================
            ))
      (values dictated-link-UDs dictated-link-MPUDs arb-UD arb-MPUD ud-nodes
                   mpud-nodes ud-links mpud-links)))

#| This finds and returns an association of a node in either UDs, UD, or tree if there is one. |#
(defunction node-assoc-UD (node UDs UD tree)
    (let ((assoc  (assoc node UDs)))
      (when (null assoc)
           (setf assoc (assoc node UD))
           (when (and (null assoc) tree)
                (setf assoc (tree-node-UD node tree))))
      assoc))

#| This finds and returns an association of a node in either MPUDs, MPUD, or tree if there is one. |#
(defunction node-assoc-MPUD (node MPUDs MPUD tree)
    (let ((assoc  (assoc node MPUDs)))
      (when (null assoc)
           (setf assoc (assoc node MPUD))
           (when (and (null assoc) tree)
                (setf assoc (tree-node-MPUD node tree))))
      assoc))

#| This finds and returns an association of a support-link in either UDs, UD, or tree if there is one. |#
(defunction link-assoc-UD (node UDs UD tree)
    (let ((assoc  (assoc node UDs)))
      (when (null assoc)
           (setf assoc (assoc node UD))
           (when (and (null assoc) tree)
                (setf assoc (tree-link-UD node tree))))
      assoc))

#| This finds and returns an association of a support-link in either MPUDs, MPUD, or tree if there is one. |#
(defunction link-assoc-MPUD (node MPUDs MPUD tree)
    (let ((assoc  (assoc node MPUDs)))
      (when (null assoc)
           (setf assoc (assoc node MPUD))
           (when (and (null assoc) tree)
                (setf assoc (tree-link-MPUD node tree))))
      assoc))

;; ----------------------------------------------------------------------

(defunction compute-triangle-set (triangle tree &optional (indent-level 0))
    (let ((triangle-set
              (make-triangle-set
                :triangle-number (incf *triangle-number*)
                :triangle-domain triangle
                :assignment-trees
                (mapcar
                  #'(lambda (ass)
                        (let ((link-UDs (setdifference (elt ass 0) (link-UDs tree)))
                                (link-MPUDs (setdifference (elt ass 1) (link-MPUDs tree)))
                                (node-UDs (setdifference (elt ass 2) (node-UDs tree)))
                                (node-MPUDs (setdifference (elt ass 3) (node-MPUDs tree))))
                        (compute-assignment-tree
                          (vector link-UDs link-MPUDs node-UDs node-MPUDs) tree  (+ 4 indent-level))))
                  (compute-assignments-to-domain tree triangle)))))
       (when *display?* (push triangle-set *creations*))
       triangle-set))

;; ----------------------------------------------------------------------

#| triangle is a triangle-domain. |#
(defunction compute-assignments-to-domain (tree triangle)
   ; (setf tr tree ia triangle) ; (break)
    ;; (step (compute-assignments-to-domain tr ia))
    (let* ((UDs nil)
              (MPUDs nil)
              (link
                (find-if
                  #'(lambda (L)
                        (setf UDs nil)
                        (setf MPUDs nil)
                        (dolist (b (support-link-basis L))
                            (let ((UD (assoc-value (tree-node-UD b tree))))
                              (cond (UD (push UD UDs) (push (assoc-value (tree-node-MPUD b tree)) MPUDs))
                                        (t (setf UDs nil) (setf MPUDs nil) (return)))))
                        UDs)
                  triangle)))
      (when (null link)
           (setf link (car triangle))
           (setf UDs
                    (mapcar
                      #'(lambda (b)
                            (maximum0
                              (mapcar
                                #'(lambda (L)
                                      (let ((tl (assoc-value (tree-link-UD L tree)))) (or tl 0.0))) (support-links b))))
                      (support-link-basis link)))
           (setf MPUDs
                    (mapcar
                      #'(lambda (b)
                            (maximum0
                              (mapcar
                                #'(lambda (L)
                                      (let ((tl (assoc-value (tree-link-MPUD L tree)))) (or tl 0.0))) (support-links b))))
                      (support-link-basis link))))
      (let* ((temp
                  (or (eq (support-link-rule link) *temporal-projection*)
                        (eq (support-link-rule link) *causal-implication*)
                        (and (not (keywordp (support-link-rule link)))
                                 (temporal? (support-link-rule link)))))
                (beta (if temp
                            (* (support-link-reason-strength link) (minimum UDs))
                            (minimum (cons (support-link-reason-strength link)  UDs))))
                (beta* (if temp
                              (* (support-link-reason-strength link) (minimum MPUDs))
                              (minimum (cons (support-link-reason-strength link) MPUDs)))))
        (multiple-value-bind
             (link-UDs1 link-MPUDs1 node-UDs1 node-MPUDs1 ud-nodes1 mpud-nodes1)
             (if (and (not (zerop beta)) (not (zerop beta*)))
               (assignment-closure (list (cons link beta)) (list (cons link beta*)) tree))
             (multiple-value-bind
                  (link-UDs3 link-MPUDs3 node-UDs3 node-MPUDs3 ud-nodes3 mpud-nodes3)
                  (assignment-closure (list (cons link 0.0)) (list (cons link 0.0)) tree)
                  (let ((assignments
                            (cond
                              (link-UDs1
                                (cond
                                  (link-UDs3
                                    (append
                                      (expand-assignment
                                        ud-nodes1 mpud-nodes1 link-UDs1 link-MPUDs1
                                        node-UDs1 node-MPUDs1 triangle tree)
                                      (expand-assignment
                                        ud-nodes3 mpud-nodes3 link-UDs3 link-MPUDs3
                                        node-UDs3 node-MPUDs3 triangle tree)))
                                  (t
                                    (expand-assignment
                                      ud-nodes1 mpud-nodes1 link-UDs1 link-MPUDs1
                                      node-UDs1 node-MPUDs1 triangle tree))))
                              (link-UDs3
                                (expand-assignment
                                  ud-nodes3 mpud-nodes3 link-UDs3 link-MPUDs3
                                  node-UDs3 node-MPUDs3 triangle tree)))))
                    (or assignments
                          (multiple-value-bind
                               (link-UDs2 link-MPUDs2 node-UDs2 node-MPUDs2 ud-nodes2 mpud-nodes2)
                               (if (not (zerop beta*))
                                 (assignment-closure (list (cons link 0.0)) (list (cons link beta*)) tree))
                               (expand-assignment
                                 ud-nodes2 mpud-nodes2 link-UDs2 link-MPUDs2
                                 node-UDs2 node-MPUDs2 triangle tree)))))))))

#| assignment is a pair (link-assignment node-assignment).  Nodes is the list of newly assigned nodes.
Candidate-links is the list of previous candidate-links that have not yet been assigned. |#
(defunction expand-assignment
    (ud-nodes mpud-nodes link-UDs link-MPUDs node-UDs node-MPUDs triangle tree)
   ; (setf u ud-nodes m mpud-nodes lu link-uds lm link-mpuds nu node-uds nm node-mpuds tr triangle t* tree)
    ;; (step (expand-assignment u m lu lm nu nm tr t*))
    (let ((candidate-links
              (subset #'(lambda (L) (or (not (assoc L link-UDs)) (not (assoc L link-MPUDs)))) triangle)))
      (cond
        ((null candidate-links)
          (list (vector link-UDs link-MPUDs node-UDs node-MPUDs)))
        (t
          (let* ((UDs nil)
                    (MPUDs nil)
                    (link
                      (find-if
                        #'(lambda (L)
                              (setf UDs nil)
                              (setf MPUDs nil)
                              (dolist (b (support-link-basis L))
                                  (let ((UD (assoc-value (node-assoc-UD b node-UDs nil tree))))
                                    (cond (UD (push UD UDs)
                                                     (push (assoc-value (node-assoc-MPUD b node-MPUDs nil tree)) MPUDs))
                                              (t (setf UDs nil) (setf MPUDs nil) (return)))))
                              UDs)
                        candidate-links)))
                       ; (intersection candidate-links
                       ;                       (unionmapcar+ #'consequent-links (union ud-nodes mpud-nodes))))))
            (when (null link)
                 (setf link (car candidate-links))
                 (setf UDs
                          (mapcar
                            #'(lambda (b)
                                  (maximum0
                                    (mapcar
                                      #'(lambda (L)
                                            (let ((tl (assoc-value (tree-link-UD L tree)))) (or tl 0.0))) (support-links b))))
                            (support-link-basis link)))
                 (setf MPUDs
                          (mapcar
                            #'(lambda (b)
                                  (maximum0
                                    (mapcar
                                      #'(lambda (L)
                                            (let ((tl (assoc-value (tree-link-MPUD L tree)))) (or tl 0.0))) (support-links b))))
                            (support-link-basis link))))
            (let* ((temp
                        (or (eq (support-link-rule link) *temporal-projection*)
                              (eq (support-link-rule link) *causal-implication*)
                              (and (not (keywordp (support-link-rule link)))
                                       (temporal? (support-link-rule link)))))
                      (beta (if temp
                                  (* (support-link-reason-strength link) (minimum UDs))
                                  (minimum (cons (support-link-reason-strength link)  UDs))))
                      (beta* (if temp
                                    (* (support-link-reason-strength link) (minimum MPUDs))
                                    (minimum (cons (support-link-reason-strength link) MPUDs)))))
              (multiple-value-bind
                   (link-UDs1 link-MPUDs1 node-UDs1 node-MPUDs1 ud-nodes1 mpud-nodes1)
                   (if (and (not (zerop beta)) (not (zerop beta*)))
                     (assignment-closure
                       (list (cons link beta)) (list (cons link beta*)) tree link-UDs link-MPUDs node-UDs node-MPUDs))
                   (multiple-value-bind
                        (link-UDs3 link-MPUDs3 node-UDs3 node-MPUDs3 ud-nodes3 mpud-nodes3)
                        (assignment-closure
                          (list (cons link 0.0)) (list (cons link 0.0)) tree link-UDs link-MPUDs node-UDs node-MPUDs)
                        (let ((assignments
                                  (cond
                                    (link-UDs1
                                      (cond
                                        (link-UDs3
                                          (append
                                            (expand-assignment
                                              ; ud-nodes1 mpud-nodes1
                                              (append ud-nodes ud-nodes1) (append mpud-nodes mpud-nodes1)
                                              link-UDs1 link-MPUDs1 node-UDs1 node-MPUDs1 triangle tree)
                                            (expand-assignment
                                              ; ud-nodes3 mpud-nodes3
                                              (append ud-nodes ud-nodes3) (append mpud-nodes mpud-nodes3)
                                              link-UDs3 link-MPUDs3 node-UDs3 node-MPUDs3 triangle tree)))
                                        (t
                                          (expand-assignment
                                            ;  ud-nodes1 mpud-nodes1
                                            (append ud-nodes ud-nodes1) (append mpud-nodes mpud-nodes1)
                                            link-UDs1 link-MPUDs1 node-UDs1 node-MPUDs1 triangle tree))))
                                    (link-UDs3
                                      (expand-assignment
                                        ; ud-nodes3 mpud-nodes3
                                        (append ud-nodes ud-nodes3) (append mpud-nodes mpud-nodes3)
                                        link-UDs3 link-MPUDs3 node-UDs3 node-MPUDs3 triangle tree)))))
                          (or assignments
                                (multiple-value-bind
                                     (link-UDs2 link-MPUDs2 node-UDs2 node-MPUDs2 ud-nodes2 mpud-nodes2)
                                     (if (not (zerop beta*))
                                       (assignment-closure
                                         (list (cons link 0.0))
                                         (list (cons link beta*)) tree link-UDs link-MPUDs node-UDs node-MPUDs))
                                     (if link-UDs2
                                       (expand-assignment
                                         ; ud-nodes2 mpud-nodes2
                                         (append ud-nodes ud-nodes2) (append mpud-nodes mpud-nodes2)
                                         link-UDs2 link-MPUDs2 node-UDs2 node-MPUDs2 triangle tree)))))))))))))

;======================================================
;                                  UPDATING-ASSIGNMENT-TREES

(defunction update-defeat-statuses ()
    ; (when (eql *cycle* 266) (break))
    ;; (step (update-defeat-statuses))
    (dolist (node
                    (unionmapcar+
                      #'(lambda (link)
                             (mem2 (inference/defeat-descendants (list link))))
                      *new-links*))
      (update-strengths node))
    (let* ((effects (compute-effects *new-links*))
              (affected-nodes (mem2 effects))
              (affected-links (mem1 effects)))
      (setf *affected-nodes* affected-nodes)
      (cond ((every #'(lambda (node)
                                   (not (some #'(lambda (d) (member d affected-links))
                                                       (node-defeatees node))))
                             affected-nodes)
                  (compute-status-assignments effects))
                (t 
                  (update-assignment-tree *new-links* *assignment-tree* effects)))))

(defunction update-strengths (node)
    (when (and (temporal-node node) (not (eql (temporal-node node) *cycle*)))
         (let ((decay (expt *temporal-decay* (- *cycle* (temporal-node node)))))
           (setf (maximal-degree-of-support node) (adjust-for-decay (maximal-degree-of-support node) decay))
           (setf (discounted-node-strength node) (adjust-for-decay (discounted-node-strength node) decay))
           (if (undefeated-degree-of-support node)
             (setf (undefeated-degree-of-support node) 
                      (adjust-for-decay (undefeated-degree-of-support node) decay)))
           (if (old-undefeated-degree-of-support node)
             (setf (old-undefeated-degree-of-support node) 
                      (adjust-for-decay (old-undefeated-degree-of-support node) decay)))
           (dolist (L (support-links node)) (compute-support-link-strength L))
           (setf (temporal-node node) *cycle*))))

(defunction compute-support-link-strength (link)
    (let ((temp (temporal-link link)))
      (cond ((and temp (not (eql temp *cycle*)))
                  (let ((decay (expt *temporal-decay* (- *cycle* temp))))
                    (setf (temporal-link link) *cycle*)
                    (when (and (not (keywordp (support-link-rule link)))
                                            (temporal? (support-link-rule link)))
                          (setf (support-link-reason-strength link)
                                     (adjust-for-decay (support-link-reason-strength link) decay)))
                    (when (support-link-strength link)
                         (setf (support-link-strength link) (adjust-for-decay (support-link-strength link) decay)))
                    ))
                (t (support-link-strength link)))))

(defunction support-link-maximal-strength (link)
    (let ((reason-strength
              (cond ((keywordp (support-link-rule link)) 1.0)
                        ((numberp (reason-strength (support-link-rule link))) (reason-strength (support-link-rule link)))
                        (t (funcall (reason-strength (support-link-rule link))
                                         (support-link-binding link) (support-link-basis link))))))
      (if (keywordp (support-link-rule link))
      (if (support-link-basis link)
          (minimum (mapcar #'maximal-degree-of-support (support-link-basis link)))
        1.0)
        (if (or (eq (support-link-rule link) *temporal-projection*)
                  (eq (support-link-rule link) *causal-implication*)
                  (and (not (keywordp (support-link-rule link))) (temporal? (support-link-rule link))))
          (* reason-strength
               (minimum (mapcar #'maximal-degree-of-support (support-link-basis link))))
          (minimum (cons reason-strength
                                      (mapcar #'maximal-degree-of-support (support-link-basis link))))))))

(defunction compute-effects (links)
    ; (when (member (support-link 11) links)  (setf l links) (break))
    ;; (step (compute-effects l))
    (setf *potential-supportees* nil *potential-link-supportees* links
             *potential-defeatees* nil *potential-link-defeatees* nil)
    (let ((new-supportees nil)
            (new-link-supportees links)
            (new-defeatees nil)
            (new-link-defeatees nil)
            (strength (maximum0 (mapcar #'support-link-maximal-strength links))))
       (loop
          (cond
            (new-supportees
              (let ((N (car new-supportees)))
                 (setf new-supportees (cdr new-supportees))
                 (dolist (L (consequent-links N))
                     (when (and (not (member L *potential-link-supportees*))
                                           (or (null (support-link-strength L))
                                                 (<<= (support-link-strength L) strength)
                                                 (some
                                                   #'(lambda (b) (<<= (undefeated-degree-of-support b)
                                                                                    strength))
                                                   (support-link-basis L))))
                          (push L *potential-link-supportees*)
                          (push L new-link-supportees)))
                 (dolist (L (node-defeatees N))
                     (when (and (not (member L *potential-link-defeatees*))
                                         (or (null (support-link-strength L))
                                               (and
                                                 (<<= (support-link-strength L) strength)
                                                 (not (some
                                                           #'(lambda (d)
                                                                 (and (undefeated-degree-of-support d)
                                                                          (>>= (undefeated-degree-of-support d)
                                                                                   (support-link-strength L))))
                                                           (support-link-defeaters L))))))
                          (push L *potential-link-defeatees*)
                          (push L new-link-defeatees)))))
            (new-defeatees
              (let ((N (car new-defeatees)))
                 (setf new-defeatees (cdr new-defeatees))
                 (dolist (L (node-defeatees N))
                     (when (and (not (member L *potential-link-supportees*))
                                           (or (null (support-link-strength L))
                                                 (<<= (support-link-strength L) strength)
                                                 (some
                                                   #'(lambda (b) (<<= (undefeated-degree-of-support b)
                                                                                    strength))
                                                   (support-link-basis L))))
                          (push L *potential-link-supportees*)
                          (push L new-link-supportees)))
                 (dolist (L (consequent-links N))
                     (when (and (not (member L *potential-link-defeatees*))
                                         (or (null (support-link-strength L))
                                               (and
                                                 (<<= (support-link-strength L) strength)
                                                 (not (some
                                                           #'(lambda (d)
                                                                 (and (undefeated-degree-of-support d)
                                                                          (>>= (undefeated-degree-of-support d)
                                                                                   (support-link-strength L))))
                                                           (support-link-defeaters L))))))
                          (push L *potential-link-defeatees*)
                          (push L new-link-defeatees)))))
            (new-link-supportees
              (let ((L (car new-link-supportees)))
                 (setf new-link-supportees (cdr new-link-supportees))
                 (let ((N (support-link-target L)))
                    (when
                         (and
                           (not (member N *potential-supportees*))
                           (or (null (undefeated-degree-of-support N))
                                 (null (support-link-strength L))
                                 (>>= (support-link-strength L) (undefeated-degree-of-support N))))
                         (push N *potential-supportees*)
                         (push N new-supportees)))))
            (new-link-defeatees
              (let ((L (car new-link-defeatees)))
                 (setf new-link-defeatees (cdr new-link-defeatees))
                 (let ((N (support-link-target L)))
                    (when
                         (and
                           (not (member N *potential-defeatees*))
                           (or (null (undefeated-degree-of-support N))
                                 (null (support-link-strength L))
                                 (>>= (support-link-strength L) (undefeated-degree-of-support N))))
                         (push N *potential-defeatees*)
                         (push N new-defeatees)))))
            (t (return))))
      (correct-for-definite-defeat-status)
       (cond
         ((not (some #'(lambda (L) (member L *potential-link-supportees*)) links))
           (list links (mapcar #'support-link-target links)))
         (t (list
               (remove-duplicates (append (append *potential-link-supportees* *potential-link-defeatees*) links))
               (remove-duplicates (append (append *potential-supportees* *potential-defeatees*)
                                                              (mapcar #'support-link-target links))))
           ))))

(defunction correct-for-definite-defeat-status ()
    (let ((new-undefeated-nodes nil)
            (new-undefeated-links nil)
            (new-unsupported-nodes nil)
            (new-unsupported-links 
              (subset
                #'(lambda (L)
                      (some
                        #'(lambda (d)
                              (and (not (member d *potential-defeatees*))
                                        (undefeated-degree-of-support d)
                                        (or
                                          (and (support-link-strength L)
                                                    (>>= (undefeated-degree-of-support d)
                                                              (support-link-strength L)))
                                          (some
                                            #'(lambda (b)
                                                   (and (undefeated-degree-of-support b)
                                                             (>>= (undefeated-degree-of-support d)
                                                                        (undefeated-degree-of-support b))))
                                            (support-link-basis L)))))
                        (support-link-defeaters L)))
                *potential-link-supportees*)))
       (setf *potential-link-supportees*
                (setdifference *potential-link-supportees* new-unsupported-links))
       ; (when
       ;     (and *display?*
       ;              (setdifference new-unsupported-links *potential-link-supportees*))
       ;     (princ "Removing potential-link-supportees:") (terpri)
       ;     (p-princ (setdifference new-unsupported-links *potential-link-supportees*)))
       (loop
          (cond
            (new-unsupported-links
              (let ((L (car new-unsupported-links)))
                 (setf new-unsupported-links (cdr new-unsupported-links))
                 (let ((N (support-link-target L)))
                    (when
                         (and
                           (member N *potential-supportees*)
                           (every
                             #'(lambda (L*)
                                   (or (eq L* L)
                                         (not (member L* *potential-link-supportees*))))
                             (support-links N)))
                         (pull N *potential-supportees*)
                        ;  (when *display?*
                        ;     (princ "Removing potential-supportee: ") (princ N) (terpri))
                         (push N new-unsupported-nodes)))))
            (new-undefeated-links
              (let ((L (car new-undefeated-links)))
                 (setf new-undefeated-links (cdr new-undefeated-links))
                 (let ((N (support-link-target L)))
                    (when
                         (and
                           (member N *potential-defeatees*)
                           (every
                             #'(lambda (L*)
                                   (or (eq L* L)
                                         (not (member L* *potential-link-defeatees*))))
                             (support-links N)))
                         (pull N *potential-defeatees*)
                         ; (when *display?*
                         ;   (princ "Removing potential-defeatee: ") (princ N) (terpri))
                         (push N new-undefeated-nodes)))))
            (new-undefeated-nodes
              (let ((N (car new-undefeated-nodes)))
                 (setf new-undefeated-nodes (cdr new-undefeated-nodes))
                 (dolist (L (consequent-links N))
                     (when
                          (and
                            (member L *potential-link-defeatees*)
                            (every
                              #'(lambda (b)
                                    (or (eq b N)
                                          (not (member b *potential-defeatees*))))
                              (support-link-basis L))
                            (every
                              #'(lambda (d)
                                    (not (member d *potential-supportees*)))
                              (support-link-defeaters L)))
                          (pull L *potential-link-defeatees*)
                         ;  (when *display?*
                         ;    (princ "Removing potential-link-defeatee: ") (princ L) (terpri))
                          (push L new-undefeated-links)))))
            (new-unsupported-nodes
              (let ((N (car new-unsupported-nodes)))
                 (setf new-unsupported-nodes (cdr new-unsupported-nodes))
                 (dolist (L (consequent-links N))
                     (when
                          (and
                            (member L *potential-link-supportees*)
                            (every
                              #'(lambda (b)
                                    (or (eq b N)
                                          (not (member b *potential-supportees*))))
                              (support-link-basis L))
                            (every
                              #'(lambda (d)
                                    (not (member d *potential-defeatees*)))
                              (support-link-defeaters L)))
                          (pull L *potential-link-supportees*)
                          ; (when *display?*
                          ;   (princ "Removing potential-link-supportee: ") (princ L) (terpri))
                          (push L new-unsupported-links)))))
            (t (return))))))

#| links is a list of support-links.  This returns the pair (link-descendants node-descendants) |#
(defunction inference/defeat-descendants
    (links &optional link-descendants node-descendants)
    (when (null link-descendants) (setf link-descendants links))
    (let ((new-descendants nil))
       (dolist (L links)
           (let ((node (support-link-target L)))
              (when (and (not (member node new-descendants))
                                    (not (member node node-descendants)))
                   (push node node-descendants)
                   (push node new-descendants))))
       (cond ((null new-descendants) (list link-descendants node-descendants))
                   (t
                     (inference/defeat-node-descendants
                       new-descendants link-descendants node-descendants)))))
           
(defunction inference/defeat-node-descendants
    (nodes &optional link-descendants node-descendants)
    (let ((new-descendants nil))
       (dolist (n nodes)
           (dolist (L (consequent-links n))
               (when (and (not (member L new-descendants))
                                     (not (member L link-descendants)))
                    (push L new-descendants)
                    (push L link-descendants)))
           (dolist (L (node-defeatees n))
               (when (and (not (member L new-descendants))
                                     (not (member L link-descendants)))
                    (push L new-descendants)
                    (push L link-descendants))))
       (cond ((null new-descendants) (list link-descendants node-descendants))
                   (t
                     (inference/defeat-descendants
                       new-descendants link-descendants node-descendants)))))

#| This returns the two values (node . UD) and (node . MPUD) if UD and MPUD are computable.  It
differs from computable-node-values in not having a consistency check. |#
(defunction new-computable-node-values (node ass-link-UD ass-link-MPUD)
    ; (setf n node tr assignment-tree au ass-link-UD am ass-link-MPUD)
    ;; (step (computable-node-values n tr au am ud mp))
    (let ((unassigned-link-UDs nil)
            (unassigned-link-MPUDs nil)
            (new-link-UD nil)
            (new-link-MPUD nil)
            (link-UDs nil)
            (link-MPUDs nil))
      (dolist (L (support-links node))
          (let ((assoc1 (link-assoc-UD L ass-link-UD nil nil))
                  (assoc2 (link-assoc-MPUD L ass-link-MPUD nil nil)))
            (cond (assoc1 (push (assoc-value assoc1) link-UDs))
                      (t (push L unassigned-link-UDs)))
            (cond (assoc2 (push (assoc-value assoc2) link-MPUDs))
                      (t (push L unassigned-link-MPUDs)))))
      (let ((new-UD (maximum0 link-UDs))
              (new-MPUD (maximum0 link-MPUDs))
              (max-link-strength
                (maximum0 (mapcar #'support-link-maximal-strength 
                                                    (union unassigned-link-UDs unassigned-link-MPUDs)))))
        (cond ((>< new-UD new-MPUD)
                    (when (>>= new-UD max-link-strength)
                         (setf new-link-UD (make-node-assoc node new-UD))
                         (setf new-link-MPUD (make-node-assoc node new-MPUD))))
                  (t  ;; This does the same as the above!!
                    (when (>>= new-UD max-link-strength)
                         (setf new-link-UD (make-node-assoc node new-UD)))
                    (when (>>= new-UD max-link-strength)
                         (setf new-link-MPUD (make-node-assoc node new-MPUD))))))
      (values new-link-UD new-link-MPUD)))

#| This returns the the two values (link . UD) and (link . MPUD) if UD and MPUD are computable.  It
differs from computable-link-values in not having a consistency check. |#
(defunction new-computable-link-values (link ass-UD ass-MPUD)
    ; (setf l link tr assignment-tree)
    ;; (step (computable-link-values l tr au am ud mp))
    (let ((basis-UDs nil)
            (basis-MPUDs nil)
            (defeater-UDs nil)
            (defeater-MPUDs nil)
            (unassigned-basis-UDs nil)
            (unassigned-basis-MPUDs nil)
            (unassigned-defeater-UDs nil)
            (unassigned-defeater-MPUDs nil)
            (new-UD nil)
            (new-MPUD nil)
            (UD nil)
            (MPUD nil)
            (node-UDs nil)
            (node-MPUDs nil))
      (dolist (b (support-link-basis link))
          (let ((value (assoc-value (node-assoc-MPUD b node-MPUDs ass-MPUD nil))))
            (cond ((eql value 0.0) (setf new-UD 0.0 new-MPUD 0.0))
                      (value (push value basis-MPUDs))
                      (t (push b unassigned-basis-MPUDs))))
          (when (null new-UD)
               (let ((value (assoc-value (node-assoc-UD b node-UDs ass-UD nil))))
                 (cond ((eql value 0.0) (setf new-UD 0.0))
                           (value (push value basis-UDs))
                           (t (push b unassigned-basis-UDs))))))
      (when new-UD (setf UD (make-link-assoc link new-UD)))
      (when new-MPUD (setf MPUD (make-link-assoc link new-MPUD)))
      ;; we may be through here
      (when (null new-MPUD)
           (let* ((temp
                       (or (eq (support-link-rule link) *temporal-projection*)
                             (eq (support-link-rule link) *causal-implication*)
                             (and (not (keywordp (support-link-rule link)))
                                      (temporal? (support-link-rule link)))))
                     (beta (if (null new-UD)
                                 (if temp
                                   (* (support-link-reason-strength link) (minimum0 basis-UDs))
                                   (minimum (cons (support-link-reason-strength link)  basis-UDs)))))
                     (beta*
                       (if temp
                         (* (support-link-reason-strength link) (minimum0 basis-MPUDs))
                         (minimum (cons (support-link-reason-strength link) basis-MPUDs)))))
             (dolist (d (support-link-defeaters link))
                 (let ((value (assoc-value (node-assoc-UD d node-UDs ass-UD nil))))
                   (cond (value
                               (when (or (>>= value beta*)
                                                 (some
                                                   #'(lambda (b)
                                                         (>>= value (maximal-degree-of-support b)))
                                                   unassigned-basis-MPUDs))
                                    (setf new-MPUD 0.0) (setf new-UD 0.0) (return))
                               (push value defeater-UDs))
                             (t (push d unassigned-defeater-UDs)))))
             (when (null new-UD)
                  (dolist (d (support-link-defeaters link))
                      (let ((value (assoc-value (node-assoc-MPUD d node-MPUDs ass-MPUD nil))))
                        (cond (value
                                    (when (or (>>= value beta)
                                                      (some
                                                        #'(lambda (b)
                                                              (>>= value (maximal-degree-of-support b)))
                                                        unassigned-basis-MPUDs))
                                         (setf new-UD 0.0) (return))
                                    (push value defeater-MPUDs))
                                  (t (push d unassigned-defeater-MPUDs))))))
             (cond (new-UD (setf UD (make-link-assoc link new-UD)))
                       ((and
                          (null unassigned-basis-UDs)
                          (every #'(lambda (delta*) (<< delta* beta)) defeater-MPUDs)
                          (every #'(lambda (d) (<< (maximal-degree-of-support d) beta))
                                      unassigned-defeater-MPUDs))
                         (setf UD (make-link-assoc link beta))))
             (cond (new-MPUD (setf MPUD (make-link-assoc link new-MPUD)))
                       ((and
                          (null unassigned-basis-MPUDs)
                          (every #'(lambda (delta) (<< delta beta*)) defeater-UDs)
                          (every #'(lambda (d) (<< (maximal-degree-of-support d) beta*))
                                      unassigned-defeater-UDs)) 
                         (setf MPUD (make-link-assoc link beta*))))))
      (values UD MPUD)))

(defunction compute-status-assignments (effects &optional assignment-tree)
    ; (setf e effects tr assignment-tree)
    ;; (step (compute-status-assignments e tr))
    (when (null assignment-tree) (setf assignment-tree *assignment-tree*))
         (let* ((affected-nodes (mem2 effects))
                   (affected-links (mem1 effects))
                   (ass-link-UD
                      (subset #'(lambda (x) (not (member (car x) affected-links)))
                                    (link-UDs assignment-tree)))
                   (ass-link-MPUD
                     (subset #'(lambda (x) (not (member (car x) affected-links)))
                                   (link-MPUDs assignment-tree)))
                   (ass-UD 
                     (subset #'(lambda (x) (not (member (car x) affected-nodes)))
                                   (node-UDs assignment-tree)))
                   (ass-MPUD
                     (subset #'(lambda (x) (not (member (car x) affected-nodes)))
                                   (node-MPUDs assignment-tree)))
                   (link-UDs nil)
                   (link-MPUDs nil)
                   (new-link-UDs nil)
                   (new-link-MPUDs nil)
                   (new-node-UDs nil)
                   (new-node-MPUDs nil)
                   (node-UDs nil)
                   (node-MPUDs nil))
      (dolist (link affected-links)
             (multiple-value-bind
                  (UD MPUD)
                  (new-computable-link-values link ass-UD ass-MPUD)
                  (when UD (push UD link-UDs) (push UD new-link-UDs))
                  (when MPUD (push MPUD link-MPUDs) (push MPUD new-link-MPUDs))
                  (when (and UD MPUD) (pull link affected-links))
             ))
      (dolist (node affected-nodes)
             (multiple-value-bind
                  (new-UD new-MPUD)
                  (new-computable-node-values node new-link-UDs new-link-MPUDs)
                  (when new-UD
                       (push new-UD node-UDs) (push new-UD new-node-UDs))
                  (when new-MPUD
                       (push new-MPUD node-MPUDs) (push new-MPUD new-node-MPUDs))
                  (when (and new-UD new-MPUD) (pull node affected-nodes))
                  ))
      (when (or link-UDs link-MPUDs node-UDs node-MPUDs)
           (cond
             ((or affected-nodes affected-links)
               (multiple-value-bind
                    (new-link-UDs new-link-MPUDs new-node-UDs new-node-MPUDs nodes links)
                    (dual-assignment-closure
                      link-UDs link-MPUDs node-UDs node-MPUDs (parent-tree assignment-tree)
                      affected-links affected-nodes ass-link-UD ass-link-MPUD ass-UD ass-MPUD)
                    (cond ((not (or new-link-UDs new-link-MPUDs new-node-UDs new-node-MPUDs))
                                (discard-assignment-tree assignment-tree))
                              (t
                                (dolist (assoc (set-difference (link-UDs assignment-tree) new-link-UDs))
                                    (let* ((L (car assoc))
                                              (UD (assoc-value assoc)))
                                      (when (eql UD 0.0)
                                           (pull assignment-tree (defeating-assignment-trees L))
                                           (push L *altered-links*))))
                                (dolist (assoc (set-difference new-link-UDs (link-UDs assignment-tree)))
                                    (let* ((L (car assoc))
                                              (UD (assoc-value assoc)))
                                      (when (eql UD 0.0)
                                           (push assignment-tree (defeating-assignment-trees L))
                                           (pushnew L *altered-links*))))
                                (setf (link-UDs assignment-tree) new-link-UDs)
                                (setf (link-MPUDs assignment-tree) new-link-MPUDs)
                                (setf (node-UDs assignment-tree) new-node-UDs)
                                (setf (node-MPUDs assignment-tree) new-node-MPUDs)
                                (setf affected-links (set-difference affected-links links))
                                (setf affected-nodes (set-difference affected-nodes nodes))))))
             (t
               (dolist (assoc new-link-UDs)
                   (let* ((L (car assoc))
                             (UD (assoc-value (assoc L (link-UDs assignment-tree)))))
                     (when (eql UD 0.0)
                          (pull assignment-tree (defeating-assignment-trees L))
                          (push L *altered-links*))
                     (when (eql (assoc-value assoc) 0.0)
                          (push assignment-tree (defeating-assignment-trees L))
                          (pushnew L *altered-links*))))
               (setf (link-UDs assignment-tree) (append new-link-UDs ass-link-UD))
               (setf (link-MPUDs assignment-tree) (append new-link-MPUDs ass-link-MPUD))
               (setf (node-UDs assignment-tree) (append new-node-UDs ass-UD))
               (setf (node-MPUDs assignment-tree) (append new-node-MPUDs ass-MPUD)))))
      (when (or affected-links affected-nodes)
           (dolist (triangle (triangle-sets assignment-tree))
               (dolist (tree (assignment-trees triangle))
                   (compute-status-assignments (list affected-links affected-nodes) tree))))))

(defunction update-assignment-tree (links tree effects &optional parent-tree)
    ; (when (eql *cycle* 41) (setf l links tr tree e effects p parent-tree) (break))
    ;; (step (update-assignment-tree l *assignment-tree* e p))
    (when parent-tree
         (setf (parent-tree tree) parent-tree))
    (when *display?* (setf *discards* nil *creations* nil))
    (let ((affected-nodes (mem2 effects))
            (affected-links (mem1 effects)))
      (cond ((and
                   (every #'(lambda (n) (null (assoc n (node-UDs tree)))) affected-nodes)
                   (every #'(lambda (L) (or (member L links) (null (assoc L (link-UDs tree)))))
                               affected-links))
                  ;; If assignment does not assign values to UD and MPUD for any members of 
                  ;; affected-nodes or affected-links other than members of links:
                  (let ((computable-UDs nil)
                          (computable-MPUDs nil))
                    (dolist (link links)
                        (multiple-value-bind (link-UD link-MPUD) (computable-link-values link tree)
                              (when link-UD (push link-UD computable-UDs))
                              (when link-MPUD (push link-MPUD computable-MPUDs))
                              (when (and link-UD link-MPUD) (pull link links))))
                       (cond
                         ;; If the values of UD(link) and MPUD(link) are computable relative to tree,
                         ;; let closure to be the assignment-closure of that assignment to link relative to tree.
                         ;; Redefine the assignment of tree  to be the result of adding closure to assignment.
                         ;; If tree has triangle-sets, apply recompute-triangle-sets to links tree nil nil.
                         ((or computable-UDs computable-MPUDs)
                           (multiple-value-bind
                                (link-UDs link-MPUDs node-UDs node-MPUDs)
                                (assignment-closure computable-UDs computable-MPUDs tree)
                                (dolist (assoc (set-difference (link-UDs tree) link-UDs))
                                    (let* ((L (car assoc))
                                              (UD (assoc-value assoc)))
                                      (when (eql UD 0.0)
                                           (pull tree (defeating-assignment-trees L))
                                           (push L *altered-links*))))
                                (dolist (assoc (set-difference link-UDs (link-UDs tree)))
                                    (let* ((L (car assoc))
                                              (UD (assoc-value assoc)))
                                      (when (eql UD 0.0)
                                           (push tree (defeating-assignment-trees L))
                                           (pushnew L *altered-links*))))
                                (setf (node-UDs tree)
                                         (append node-UDs
                                                        (subset
                                                          #'(lambda (x) (null (assoc (car x) node-UDs))) (node-UDs tree))))
                                (setf (node-MPUDs tree)
                                         (append node-MPUDs
                                                        (subset
                                                          #'(lambda (x) (null (assoc (car x) node-MPUDs))) (node-MPUDs tree))))
                                (setf (link-UDs tree)
                                         (append link-UDs
                                                        (subset
                                                          #'(lambda (x) (null (assoc (car x) link-UDs))) (link-UDs tree))))
                                (setf (link-MPUDs tree)
                                         (append link-MPUDs
                                                        (subset
                                                          #'(lambda (x) (null (assoc (car x) link-MPUDs))) (link-MPUDs tree))))
                                (recompute-triangle-sets links tree (list nil nil))))
                         (t
                           ;; If the values of UD(link) and MPUD(link) are not computable relative to tree, 
                           ;; apply update-triangle-set to link, triangle-set, affected-nodes, affected-links, 
                           ;; and tree for each triangle-set of tree.
                           (dolist (triangle-set (triangle-sets tree))
                               (update-triangle-set links triangle-set effects tree))))))
                (t
                  ;; Otherwise, let ass0 be the assignment to the unaffected-nodes and unaffected-links
                  ;; that are in the domain of assignment.
                  (let* ((node-UD0
                              (subset #'(lambda (assoc) (not (member (car assoc) affected-nodes)))
                                            (node-UDs tree)))
                            (node-MPUD0
                              (subset #'(lambda (assoc) (not (member (car assoc) affected-nodes)))
                                            (node-MPUDs tree)))
                            (link-UD0
                              (subset #'(lambda (assoc) (not (member (car assoc) affected-links)))
                                            (link-UDs tree)))
                            (link-MPUD0
                              (subset #'(lambda (assoc) (not (member (car assoc) affected-links)))
                                            (link-MPUDs tree)))
                            (link-UDs nil)
                            (link-MPUDs nil)
                            (node-UDs nil)
                            (node-MPUDs nil)
                            (computed-nodes nil)
                            (computed-links nil))
                    (dolist (link affected-links)
                        (multiple-value-bind
                             (UD MPUD)
                             (computable-link-values
                               link (parent-tree tree) link-UD0 link-MPUD0 node-UD0 node-MPUD0)
                             (when UD (push UD link-UDs) (push link computed-links))
                             (when MPUD (push MPUD link-MPUDs))))
                    (dolist (node affected-nodes)
                        (multiple-value-bind
                             (new-UD new-MPUD)
                             (computable-node-values
                               node (parent-tree tree) link-UD0 link-MPUD0 node-UD0 node-MPUD0)
                             (when new-UD (push new-UD node-UDs) (push node computed-nodes))
                             (when new-MPUD (push new-MPUD node-MPUDs))))
                    (cond ((or link-UDs link-MPUDs node-UDs node-MPUDs)
                                ;; If some affected-nodes or affected-links have computable UD's or MPUD's in
                                ;; ass0, let closure be the assignment-closure of those computable values relative
                                ;; to ass0.
                                (multiple-value-bind
                                     (link-UDs link-MPUDs node-UDs node-MPUDs ud-nodes mpud-nodes ud-links mpud-links)
                                     (dual-assignment-closure
                                       link-UDs link-MPUDs node-UDs node-MPUDs (parent-tree tree)
                                       affected-links affected-nodes link-UD0 link-MPUD0 node-UD0 node-MPUD0)
                                     (cond
                                       ;; If closure agrees with assignment for all nodes and links in the domain of 
                                       ;; closure, delete from affected-nodes and affected-links all those assigned UD's
                                       ;; and MPUD's by closure.
                                       ((and (every
                                                  #'(lambda (n)
                                                        (let ((assoc (assoc n node-UDs)))
                                                          (or (null assoc)
                                                                (let ((assoc* (assoc n (node-UDs tree))))
                                                                  (and assoc* (>< (assoc-value assoc) (assoc-value assoc*)))))))
                                                  affected-nodes)
                                                 (every
                                                   #'(lambda (n)
                                                         (let ((assoc (assoc n node-MPUDs)))
                                                          (or (null assoc)
                                                                (let ((assoc* (assoc n (node-MPUDs tree))))
                                                                  (and assoc* (>< (assoc-value assoc) (assoc-value assoc*)))))))
                                                   affected-nodes)
                                                 (every
                                                   #'(lambda (L)
                                                        (let ((assoc (assoc L link-UDs)))
                                                          (or (null assoc)
                                                                (let ((assoc* (assoc L (link-UDs tree))))
                                                                  (and assoc* (>< (assoc-value assoc) (assoc-value assoc*)))))))
                                                   affected-links)
                                                 (every
                                                   #'(lambda (L)
                                                         (let ((assoc (assoc L link-MPUDs)))
                                                          (or (null assoc)
                                                                (let ((assoc* (assoc L (link-MPUDs tree))))
                                                                  (and assoc* (>< (assoc-value assoc) (assoc-value assoc*)))))))
                                                   affected-links))
                                         (setf affected-nodes
                                                  (set-difference
                                                    affected-nodes
                                                    (append (intersection ud-nodes mpud-nodes) computed-nodes)))
                                         (setf affected-links
                                                  (set-difference
                                                    affected-links
                                                    (append (intersection ud-links mpud-links) computed-links)))
                                         (cond
                                           ;; If the domain of closure is a proper subset of the domain of assignment,
                                           ;; redefine the assignment of tree to be closure, and apply recompute-triangle-sets
                                           ;; to link tree affected-nodes affected-links.
                                           ((or (some
                                                    #'(lambda (n) (and (assoc n (node-UDs tree)) (not (assoc n node-UDs))))
                                                    affected-nodes)
                                                  (some
                                                    #'(lambda (n) (and (assoc n (node-UDs tree)) (not (assoc n node-UDs))))
                                                    affected-nodes)
                                                  (some
                                                    #'(lambda (n) (and (assoc n (node-UDs tree)) (not (assoc n node-UDs))))
                                                    affected-nodes)
                                                  (some
                                                    #'(lambda (n) (and (assoc n (node-UDs tree)) (not (assoc n node-UDs))))
                                                    affected-nodes))
                                             (dolist (assoc (set-difference (link-UDs tree) link-UDs))
                                                 (let* ((L (car assoc))
                                                           (UD (assoc-value assoc)))
                                                   (when (eql UD 0.0)
                                                        (pull tree (defeating-assignment-trees L))
                                                        (push L *altered-links*))))
                                             (dolist (assoc (set-difference link-UDs (link-UDs tree)))
                                                 (let* ((L (car assoc))
                                                           (UD (assoc-value assoc)))
                                                   (when (eql UD 0.0)
                                                        (push tree (defeating-assignment-trees L))
                                                        (pushnew L *altered-links*))))
                                             (setf (node-UDs tree) node-UDs)
                                             (setf (node-MPUDs tree) node-MPUDs)
                                             (setf (link-UDs tree) link-UDs)
                                             (setf (link-MPUDs tree) link-MPUDs)
                                             (recompute-triangle-sets links tree (list affected-links affected-nodes)))
                                           (t
                                             ;; If instead the domain of closure is is the same as the domain of assignment,
                                             ;; and there are some affected-nodes or affected-links left, apply 
                                             ;; update-triangle-set to link, triangle-set, affected-nodes, affected-links,
                                             ;; and tree for each triangle-set of tree.
                                             (if (or affected-nodes affected-links)
                                               (dolist (triangle (triangle-sets tree))
                                                   (update-triangle-set links triangle (list affected-links affected-nodes) tree))))))
                                       (t
                                         ;; Otherwise, redefine the assignment of tree to be closure.  Delete from
                                         ;; affected-nodes and affected-links all those assigned UD's and MPUD's by
                                         ;; closure, and apply recompute-triangle-sets to link, tree affected-nodes
                                         ;; and affected-links.
                                         (dolist (assoc (set-difference (link-UDs tree) link-UDs))
                                             (let* ((L (car assoc))
                                                       (UD (assoc-value assoc)))
                                               (when (eql UD 0.0)
                                                    (pull tree (defeating-assignment-trees L))
                                                    (push L *altered-links*))))
                                         (dolist (assoc (set-difference link-UDs (link-UDs tree)))
                                             (let* ((L (car assoc))
                                                       (UD (assoc-value assoc)))
                                               (when (eql UD 0.0)
                                                    (push tree (defeating-assignment-trees L))
                                                    (pushnew L *altered-links*))))
                                         (setf (node-UDs tree) node-UDs)
                                         (setf (node-MPUDs tree) node-MPUDs)
                                         (setf (link-UDs tree) link-UDs)
                                         (setf (link-MPUDs tree) link-MPUDs)
                                         (setf affected-nodes
                                                  (set-difference
                                                    affected-nodes
                                                    (append (intersection ud-nodes mpud-nodes) computed-nodes)))
                                         (setf affected-links
                                                  (set-difference
                                                    affected-links
                                                    (append (intersection ud-links mpud-links) computed-links)))
                                         (recompute-triangle-sets links tree (list affected-links affected-nodes))))))
                              (t
                                ;; If instead no affected-nodes or affected-links have computable UD's or MPUD's 
                                ;; in ass0, redefine the assignment of tree to be ass0, and apply recompute-triangle-sets
                                ;; to link tree affected-nodes affected-links.
                                (dolist (assoc (set-difference (link-UDs tree) link-UD0))
                                    (let* ((L (car assoc))
                                              (UD (assoc-value assoc)))
                                      (when (eql UD 0.0)
                                           (pull tree (defeating-assignment-trees L))
                                           (push L *altered-links*))))
                                (setf (node-UDs tree) node-UD0)
                                (setf (node-MPUDs tree) node-MPUD0)
                                (setf (link-UDs tree) link-UD0)
                                (setf (link-MPUDs tree) link-MPUD0)
                                (recompute-triangle-sets links tree effects))
                              ))))))

#| This returns the two values (node . UD) and (node . MPUD) if UD and MPUD are computable. |#
(defunction computable-node-values
    (node assignment-tree &optional ass-link-UD ass-link-MPUD ass-UD ass-MPUD)
    ; (setf n node tr assignment-tree au ass-link-UD am ass-link-MPUD ud ass-UD mp ass-MPUD)
    ;; (step (computable-node-values n tr au am ud mp))
    (let ((unassigned-link-UDs nil)
            (unassigned-link-MPUDs nil)
            (new-link-UD nil)
            (new-link-MPUD nil)
            (link-UDs nil)
            (link-MPUDs nil))
      (dolist (L (support-links node))
          (let ((assoc1 (link-assoc-UD L ass-link-UD nil assignment-tree))
                  (assoc2 (link-assoc-MPUD L ass-link-MPUD nil assignment-tree)))
            (cond (assoc1 (push (assoc-value assoc1) link-UDs))
                      (t (push L unassigned-link-UDs)))
            (cond (assoc2 (push (assoc-value assoc2) link-MPUDs))
                      (t (push L unassigned-link-MPUDs)))))
      (let ((new-UD (maximum0 link-UDs))
              (new-MPUD (maximum0 link-MPUDs))
              (max-link-strength
                (maximum0 (mapcar #'support-link-maximal-strength 
                                                    (union unassigned-link-UDs unassigned-link-MPUDs)))))
        (cond ((>< new-UD new-MPUD)
                    (when (>>= new-UD max-link-strength)
                         (let ((node-UD (assoc-value (node-assoc-UD node ass-UD nil assignment-tree)))
                                 (node-MPUD (assoc-value (node-assoc-MPUD node ass-MPUD nil assignment-tree))))
                           (cond (node-UD
                                       (if (or (not (>< node-UD new-UD)) (not (>< node-MPUD new-MPUD)))
                                         (throw 'consistency-check nil)))
                                     (t
                                       (setf new-link-UD (make-node-assoc node new-UD))
                                       (setf new-link-MPUD (make-node-assoc node new-MPUD)))))))
                  (t
                    (when (>>= new-UD max-link-strength)
                         (let ((node-UD (assoc-value (node-assoc-UD node ass-UD nil assignment-tree))))
                           (cond (node-UD
                                       (if (not (>< node-UD new-UD)) (throw 'consistency-check nil)))
                                     (t
                                       (setf new-link-UD (make-node-assoc node new-UD))))))
                    (when (>>= new-UD max-link-strength)
                         (let ((node-MPUD (assoc-value (node-assoc-MPUD node ass-MPUD nil assignment-tree))))
                           (cond (node-MPUD
                                       (if (not (>< node-MPUD new-MPUD)) (throw 'consistency-check nil)))
                                     (t
                                       (setf new-link-MPUD (make-node-assoc node new-MPUD)))))))))
      (values new-link-UD new-link-MPUD)))

#| This returns the the two values (link . UD) and (link . MPUD) if UD and MPUD are computable. |#
(defunction computable-link-values
    (link assignment-tree &optional ass-link-UD ass-link-MPUD ass-UD ass-MPUD)
    ; (setf l link tr assignment-tree au ass-link-UD am ass-link-MPUD ud ass-UD mp ass-MPUD)
    ;; (step (computable-link-values l tr au am ud mp))
    (let ((basis-UDs nil)
            (basis-MPUDs nil)
            (defeater-UDs nil)
            (defeater-MPUDs nil)
            (unassigned-basis-UDs nil)
            (unassigned-basis-MPUDs nil)
            (unassigned-defeater-UDs nil)
            (unassigned-defeater-MPUDs nil)
            (new-UD nil)
            (new-MPUD nil)
            (UD nil)
            (MPUD nil)
            (node-UDs ass-UD)
            (node-MPUDs ass-MPUD)
            (link-UDs ass-link-UD)
            (link-MPUDs ass-link-MPUD))
      (dolist (b (support-link-basis link))
          (let ((value (assoc-value (node-assoc-MPUD b node-MPUDs nil assignment-tree))))
            (cond ((eql value 0.0) (setf new-UD 0.0 new-MPUD 0.0))
                      (value (push value basis-MPUDs))
                      (t (push b unassigned-basis-MPUDs))))
          (when (null new-UD)
               (let ((value (assoc-value (node-assoc-UD b node-UDs nil assignment-tree))))
                 (cond ((eql value 0.0) (setf new-UD 0.0))
                           (value (push value basis-UDs))
                           (t (push b unassigned-basis-UDs))))))
      (when new-UD
           (let ((link-UD (assoc-value (link-assoc-UD link link-UDs nil assignment-tree))))
             (cond (link-UD
                         (if (not (>< link-UD new-UD))
                           (throw 'consistency-check nil)))
                       (t
                         (setf UD (make-link-assoc link new-UD))))))
      (when new-MPUD
           (let ((link-MPUD (assoc-value (link-assoc-MPUD link link-MPUDs nil assignment-tree))))
             (cond (link-MPUD
                         (if (not (>< link-MPUD new-MPUD))
                           (throw 'consistency-check nil)))
                       (t
                         (setf MPUD (make-link-assoc link new-MPUD))))))
      ;; we may be through here
      (when (null new-MPUD)
           (let* ((temp
                       (or (eq (support-link-rule link) *temporal-projection*)
                             (eq (support-link-rule link) *causal-implication*)
                             (and (not (keywordp (support-link-rule link)))
                                      (temporal? (support-link-rule link)))))
                     (beta (if (null new-UD)
                                 (if temp
                                   (* (support-link-reason-strength link) (minimum0 basis-UDs))
                                   (minimum (cons (support-link-reason-strength link)  basis-UDs)))))
                     (beta*
                       (if temp
                         (* (support-link-reason-strength link) (minimum0 basis-MPUDs))
                         (minimum (cons (support-link-reason-strength link) basis-MPUDs)))))
             (dolist (d (support-link-defeaters link))
                 (let ((value (assoc-value (node-assoc-UD d node-UDs nil assignment-tree))))
                   (cond (value
                               (when (or (>>= value beta*)
                                                 (some
                                                   #'(lambda (b)
                                                         (>>= value (maximal-degree-of-support b)))
                                                   unassigned-basis-MPUDs))
                                    (setf new-MPUD 0.0) (setf new-UD 0.0) (return))
                               (push value defeater-UDs))
                             (t (push d unassigned-defeater-UDs)))))
             (when (null new-UD)
                  (dolist (d (support-link-defeaters link))
                      (let ((value (assoc-value (node-assoc-MPUD d node-MPUDs nil assignment-tree))))
                        (cond (value
                                    (when (or (>>= value beta)
                                                      (some
                                                        #'(lambda (b)
                                                              (>>= value (maximal-degree-of-support b)))
                                                        unassigned-basis-MPUDs))
                                         (setf new-UD 0.0) (return))
                                    (push value defeater-MPUDs))
                                  (t (push d unassigned-defeater-MPUDs))))))
             (cond (new-UD
                         (let ((link-UD (assoc-value (link-assoc-UD link link-UDs nil assignment-tree))))
                           (cond (link-UD
                                       (if (not (>< link-UD new-UD))
                                         (throw 'consistency-check nil)))
                                     (t
                                       (setf UD (make-link-assoc link new-UD))))))
                       ((and
                          (null unassigned-basis-UDs)
                          (every #'(lambda (delta*) (<< delta* beta)) defeater-MPUDs)
                          (every #'(lambda (d) (<< (maximal-degree-of-support d) beta))
                                      unassigned-defeater-MPUDs))
                         (let ((link-UD (assoc-value (link-assoc-UD link link-UDs nil assignment-tree))))
                           (cond (link-UD
                                       (if (not (>< link-UD beta))
                                         (throw 'consistency-check nil)))
                                     (t
                                       (setf UD (make-link-assoc link beta)))))))
             (cond (new-MPUD
                         (let ((link-MPUD (assoc-value (link-assoc-MPUD link link-MPUDs nil assignment-tree))))
                           (cond (link-MPUD
                                       (if (not (>< link-MPUD new-MPUD))
                                         (throw 'consistency-check nil)))
                                     (t
                                       (setf MPUD (make-link-assoc link new-MPUD))))))
                       ((and
                          (null unassigned-basis-MPUDs)
                          (every #'(lambda (delta) (<< delta beta*)) defeater-UDs)
                          (every #'(lambda (d) (<< (maximal-degree-of-support d) beta*))
                                      unassigned-defeater-UDs))
                         (let ((link-MPUD (assoc-value (link-assoc-MPUD link link-MPUDs nil assignment-tree))))
                           (cond (link-MPUD
                                       (if (not (>< link-MPUD beta*))
                                         (throw 'consistency-check nil)))
                                     (t
                                       (setf MPUD (make-link-assoc link beta*)))))))))
      (values UD MPUD)))

(defunction recompute-triangle-sets (links tree effects)
    (let* ((triangle-sets (triangle-sets tree))
              (domains (compute-triangle-domains tree)))
       (setf (triangle-sets tree) nil)
       (dolist (domain domains)
           (let ((old-triangle
                     (find-if
                       #'(lambda (triangle)
                             (and (subsetp= domain (triangle-domain triangle))
                                       (subsetp= (triangle-domain triangle) domain)))
                       triangle-sets)))
             (cond (old-triangle
                         (pull old-triangle triangle-sets)
                         (push old-triangle (triangle-sets tree))
                         (cond ((or (mem1 effects) (mem2 effects))
                              (update-triangle-set links old-triangle effects tree))))
                          (t 
                            (let ((triangle-set (compute-triangle-set domain tree)))
                               (push triangle-set (triangle-sets tree)))))))
       (dolist (triangle triangle-sets) (discard-triangle-set triangle tree))))

#| This removes triangle from the triangle-sets of tree, and deletes all sub-trees of triangle
from the lists of assignment-trees for nodes to which they assign values. |#
(defunction discard-triangle-set (triangle tree)
    (when *display?* (push triangle *discards*))
    (pull triangle (triangle-sets tree))
    (dolist (tree* (assignment-trees triangle))
        (discard-assignment-tree tree*)))

(defunction discard-assignment-tree (tree)
    (dolist (assoc (link-UDS tree))
        (when (zerop (assoc-value assoc))
             (pull tree (defeating-assignment-trees (car assoc)))
             (push (car assoc) *altered-links*)))
    (dolist (triangle (triangle-sets tree))
        (discard-triangle-set triangle tree)))

(defunction update-triangle-set (links triangle-set effects tree)
    (let ((domain (triangle-domain triangle-set))
            (affected-nodes (mem2 effects))
            (affected-links (mem1 effects)))
       (cond ((and
                     (disjointp domain affected-links)
                     (every
                       #'(lambda (L)
                             (and (disjoint affected-nodes (support-link-basis L))
                                       (disjoint affected-nodes (support-link-defeaters L))))
                       domain))
                    (dolist (assignment-tree (assignment-trees triangle-set))
                        (update-assignment-tree links assignment-tree effects tree)))
                   (t
                     (let* ((n (mem1 domain))
                               (new-domain
                                 (cons n (remove n (inference/defeat-ancestors domain tree))))
                               (new-triangle-set
                                 (compute-triangle-set new-domain tree)))
                        (discard-triangle-set triangle-set tree)
                        (push new-triangle-set (triangle-sets tree)))))))
