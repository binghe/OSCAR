(in-package "OSCAR")

==============================================
Definition overwritten 7/17/2014     9:9:2
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION &OPTIONAL GENERATING-NODE)
  (COND ((OR (BACKWARDS-PREMISES REASON)
             (BACKWARDS-PREMISES-FUNCTION REASON))
         (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES
                                          INSTANTIATIONS
                                          REASON
                                          INTEREST
                                          DEPTH
                                          PRIORITY
                                          BINDING
                                          SUPPOSITION
                                          :GENERATING-NODE
                                          GENERATING-NODE
                                          :REMAINING-PREMISES
                                          (BACKWARDS-PREMISES REASON)
                                          :CLUES
                                          CLUES))
        ((OR (NUMBERP (REASON-STRENGTH REASON))
             (>= (FUNCALL (REASON-STRENGTH REASON)
                          BINDING
                          SUPPORTING-NODES)
                 (DEGREE-OF-INTEREST INTEREST)))
         (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
           (DRAW-CONCLUSION (CAR P)
                            SUPPORTING-NODES
                            REASON
                            INSTANTIATIONS
                            (DISCOUNT-FACTOR REASON)
                            DEPTH
                            NIL
                            (CDR P)
                            :BINDING
                            BINDING
                            :CLUES
                            CLUES)))))

==============================================
Definition overwritten 7/17/2014     9:48:9
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
       (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES
        INSTANTIATIONS SUPPOSITION &OPTIONAL GENERATING-NODE)
  (COND ((OR (BACKWARDS-PREMISES REASON)
             (BACKWARDS-PREMISES-FUNCTION REASON))
         (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES
                                          INSTANTIATIONS
                                          REASON
                                          INTEREST
                                          DEPTH
                                          PRIORITY
                                          BINDING
                                          SUPPOSITION
                                          :GENERATING-NODE
                                          GENERATING-NODE
                                          :REMAINING-PREMISES
                                          (BACKWARDS-PREMISES REASON)
                                          :CLUES
                                          CLUES))
        ((OR (NUMBERP (REASON-STRENGTH REASON))
             (>= (FUNCALL (REASON-STRENGTH REASON)
                          BINDING
                          SUPPORTING-NODES)
                 (DEGREE-OF-INTEREST INTEREST)))
         (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
           (DRAW-CONCLUSION (CAR P)
                            SUPPORTING-NODES
                            REASON
                            INSTANTIATIONS
                            (DISCOUNT-FACTOR REASON)
                            DEPTH
                            NIL
                            (CDR P)
                            :BINDING
                            BINDING
                            :CLUES
                            CLUES)))))

==============================================
Definition overwritten 12/13/2015     23:46:53
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE :REMAINING-PREMISES
    (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON)) (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES) (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 12/19/2015     8:42:29
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE :REMAINING-PREMISES
    (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON)) (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES) (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 12/26/2015     12:15:44
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
 (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS
  SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST
    DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE
    :REMAINING-PREMISES (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON))
    (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
     (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
     (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 12/26/2015     12:16:8
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
 (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS
  SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST
    DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE
    :REMAINING-PREMISES (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON))
    (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
     (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
     (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 12/26/2015     12:27:6
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
 (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS
  SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST
    DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE
    :REMAINING-PREMISES (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON))
    (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
     (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
     (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 12/26/2015     13:5:7
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
 (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS
  SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST
    DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE
    :REMAINING-PREMISES (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON))
    (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
     (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
     (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 12/26/2015     14:17:7
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE :REMAINING-PREMISES
    (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON)) (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES) (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 12/26/2015     15:16:17
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE :REMAINING-PREMISES
    (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON)) (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES) (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 1/21/2016     17:31:57
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
 (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS
  SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST
    DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE
    :REMAINING-PREMISES (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON))
    (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
     (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
     (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 1/31/2016     21:32:10
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE :REMAINING-PREMISES
    (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON)) (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES) (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 1/31/2016     21:34:22
--------------------------------------------------------------------------------
(DEFUN UPDATE-PERCEPTS NIL (DOLIST (INPUT (E-ASSOC *CYCLE* *INPUTS*)) (APPLY #'FORM-PERCEPT INPUT)))

==============================================
Definition overwritten 2/5/2016     11:3:36
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE
 (REASON BINDING INTEREST DEPTH PRIORITY SUPPORTING-NODES CLUES INSTANTIATIONS
  SUPPOSITION &OPTIONAL GENERATING-NODE)
 (COND
  ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
   (CONSTRUCT-INITIAL-INTEREST-LINK SUPPORTING-NODES INSTANTIATIONS REASON INTEREST
    DEPTH PRIORITY BINDING SUPPOSITION :GENERATING-NODE GENERATING-NODE
    :REMAINING-PREMISES (BACKWARDS-PREMISES REASON) :CLUES CLUES))
  ((OR (NUMBERP (REASON-STRENGTH REASON))
    (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
     (DEGREE-OF-INTEREST INTEREST)))
   (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
    (DRAW-CONCLUSION (CAR P) SUPPORTING-NODES REASON INSTANTIATIONS
     (DISCOUNT-FACTOR REASON) DEPTH NIL (CDR P) :BINDING BINDING :CLUES CLUES)))))

==============================================
Definition overwritten 2/5/2016     11:6:2
--------------------------------------------------------------------------------
(DEFUN UPDATE-PERCEPTS NIL
 (DOLIST (INPUT (E-ASSOC *CYCLE* *INPUTS*)) (APPLY #'FORM-PERCEPT INPUT)))

==============================================
Definition overwritten 2/5/2016     11:6:21
--------------------------------------------------------------------------------
(DEFUN UPDATE-PERCEPTS NIL
 (DOLIST (INPUT *INPUTS*)
  (WHEN (EQ (CAR INPUT) *CYCLE*) (APPLY #'FORM-PERCEPT (CDR INPUT)))))

==============================================
Definition overwritten 2/5/2016     11:6:21
--------------------------------------------------------------------------------
(DEFUN UPDATE-PERCEPTS NIL
 (DOLIST (INPUT (E-ASSOC *CYCLE* *INPUTS*)) (APPLY #'FORM-PERCEPT INPUT)))

==============================================
Definition overwritten 2/5/2016     11:7:18
--------------------------------------------------------------------------------
(DEFUN UPDATE-PERCEPTS NIL
 (DOLIST (INPUT *INPUTS*)
  (WHEN (EQ (CAR INPUT) *CYCLE*) (APPLY #'FORM-PERCEPT (CDR INPUT)))))

==============================================
Definition overwritten 2/5/2016     11:7:18
--------------------------------------------------------------------------------
(DEFUN UPDATE-PERCEPTS NIL
 (DOLIST (INPUT (E-ASSOC *CYCLE* *INPUTS*)) (APPLY #'FORM-PERCEPT INPUT)))

==============================================
Definition overwritten 8/25/2017     11:39:18
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY
                                 SUPPORTING-NODES CLUES INSTANTIATIONS
                                 SUPPOSITION &OPTIONAL GENERATING-NODE)
  (COND ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
         (CONSTRUCT-INITIAL-INTEREST-LINK
           SUPPORTING-NODES
           INSTANTIATIONS
           REASON
           INTEREST
           DEPTH
           PRIORITY
           BINDING
           SUPPOSITION
           :GENERATING-NODE
           GENERATING-NODE
           :REMAINING-PREMISES
           (BACKWARDS-PREMISES REASON)
           :CLUES
           CLUES))
        ((OR (NUMBERP (REASON-STRENGTH REASON))
             (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
                 (DEGREE-OF-INTEREST INTEREST)))
         (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
           (DRAW-CONCLUSION
             (CAR P)
             SUPPORTING-NODES
             REASON
             INSTANTIATIONS
             (DISCOUNT-FACTOR REASON)
             DEPTH
             NIL
             (CDR P)
             :BINDING
             BINDING
             :CLUES
             CLUES)))))

==============================================
Definition overwritten 8/25/2017     11:39:58
--------------------------------------------------------------------------------
(DEFUN FLASH-TERMINAL-DEDUCTIVE-ANCESTORS (SELECTED-NODE WIND)
  (FLASH-NODES (SUBSET #'(LAMBDA (N) (ASSOC N (NODE-LIST WIND)))
                       (COMPUTE-TERMINAL-DEDUCTIVE-ANCESTORS SELECTED-NODE))
               WIND
               *BLUE-COLOR*
               5
               (CAT-LIST (LIST "Node "
                               (WRITE-TO-STRING
                                 (INFERENCE-NUMBER SELECTED-NODE))
                               " has no terminal-deductive-ancestors")))
  (WHEN (NOT (SHIFT-KEY-P)) (SETF *FLASH-TERMINAL-DEDUCTIVE-ANCESTORS* NIL)))

==============================================
Definition overwritten 8/25/2017     13:41:35
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY
                                 SUPPORTING-NODES CLUES INSTANTIATIONS
                                 SUPPOSITION &OPTIONAL GENERATING-NODE)
  (COND ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
         (CONSTRUCT-INITIAL-INTEREST-LINK
           SUPPORTING-NODES
           INSTANTIATIONS
           REASON
           INTEREST
           DEPTH
           PRIORITY
           BINDING
           SUPPOSITION
           :GENERATING-NODE
           GENERATING-NODE
           :REMAINING-PREMISES
           (BACKWARDS-PREMISES REASON)
           :CLUES
           CLUES))
        ((OR (NUMBERP (REASON-STRENGTH REASON))
             (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
                 (DEGREE-OF-INTEREST INTEREST)))
         (COND ((CONCLUSIONS-FUNCTION REASON)
                (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
                  (DRAW-CONCLUSION
                    (CAR P)
                    SUPPORTING-NODES
                    REASON
                    INSTANTIATIONS
                    (DISCOUNT-FACTOR REASON)
                    DEPTH
                    NIL
                    (CDR P)
                    :BINDING
                    BINDING
                    :CLUES
                    CLUES)))
               (T
                (DRAW-CONCLUSION
                  (INTEREST-FORMULA INTEREST)
                  SUPPORTING-NODES
                  REASON
                  INSTANTIATIONS
                  (DISCOUNT-FACTOR REASON)
                  DEPTH
                  NIL
                  (DEFEASIBLE-RULE REASON)
                  :BINDING
                  BINDING
                  :CLUES
                  CLUES))))))

==============================================
Definition overwritten 8/25/2017     13:41:35
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY
                                 SUPPORTING-NODES CLUES INSTANTIATIONS
                                 SUPPOSITION &OPTIONAL GENERATING-NODE)
  (COND ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
         (CONSTRUCT-INITIAL-INTEREST-LINK
           SUPPORTING-NODES
           INSTANTIATIONS
           REASON
           INTEREST
           DEPTH
           PRIORITY
           BINDING
           SUPPOSITION
           :GENERATING-NODE
           GENERATING-NODE
           :REMAINING-PREMISES
           (BACKWARDS-PREMISES REASON)
           :CLUES
           CLUES))
        ((OR (NUMBERP (REASON-STRENGTH REASON))
             (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
                 (DEGREE-OF-INTEREST INTEREST)))
         (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
           (DRAW-CONCLUSION
             (CAR P)
             SUPPORTING-NODES
             REASON
             INSTANTIATIONS
             (DISCOUNT-FACTOR REASON)
             DEPTH
             NIL
             (CDR P)
             :BINDING
             BINDING
             :CLUES
             CLUES)))))

==============================================
Definition overwritten 8/25/2017     13:41:42
--------------------------------------------------------------------------------
(DEFUN FLASH-TERMINAL-DEDUCTIVE-ANCESTORS (SELECTED-NODE WIND)
  (FLASH-NODES (SUBSET #'(LAMBDA (N) (ASSOC N (NODE-LIST WIND)))
                       (COMPUTE-TERMINAL-DEDUCTIVE-ANCESTORS SELECTED-NODE))
               WIND
               *BLUE-COLOR*
               5
               (CAT-LIST (LIST "Node "
                               (WRITE-TO-STRING
                                 (INFERENCE-NUMBER SELECTED-NODE))
                               " has no terminal-deductive-ancestors")))
  (SETF *FLASH-ANCESTORS* NIL))

==============================================
Definition overwritten 8/25/2017     13:41:43
--------------------------------------------------------------------------------
(DEFUN FLASH-TERMINAL-DEDUCTIVE-ANCESTORS (SELECTED-NODE WIND)
  (FLASH-NODES (SUBSET #'(LAMBDA (N) (ASSOC N (NODE-LIST WIND)))
                       (COMPUTE-TERMINAL-DEDUCTIVE-ANCESTORS SELECTED-NODE))
               WIND
               *BLUE-COLOR*
               5
               (CAT-LIST (LIST "Node "
                               (WRITE-TO-STRING
                                 (INFERENCE-NUMBER SELECTED-NODE))
                               " has no terminal-deductive-ancestors")))
  (WHEN (NOT (SHIFT-KEY-P)) (SETF *FLASH-TERMINAL-DEDUCTIVE-ANCESTORS* NIL)))

==============================================
Definition overwritten 8/25/2017     13:53:42
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY
                                 SUPPORTING-NODES CLUES INSTANTIATIONS
                                 SUPPOSITION &OPTIONAL GENERATING-NODE)
  (COND ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
         (CONSTRUCT-INITIAL-INTEREST-LINK
           SUPPORTING-NODES
           INSTANTIATIONS
           REASON
           INTEREST
           DEPTH
           PRIORITY
           BINDING
           SUPPOSITION
           :GENERATING-NODE
           GENERATING-NODE
           :REMAINING-PREMISES
           (BACKWARDS-PREMISES REASON)
           :CLUES
           CLUES))
        ((OR (NUMBERP (REASON-STRENGTH REASON))
             (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
                 (DEGREE-OF-INTEREST INTEREST)))
         (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
           (DRAW-CONCLUSION
             (CAR P)
             SUPPORTING-NODES
             REASON
             INSTANTIATIONS
             (DISCOUNT-FACTOR REASON)
             DEPTH
             NIL
             (CDR P)
             :BINDING
             BINDING
             :CLUES
             CLUES)))))

==============================================
Definition overwritten 8/25/2017     14:3:9
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY
                                 SUPPORTING-NODES CLUES INSTANTIATIONS
                                 SUPPOSITION &OPTIONAL GENERATING-NODE)
  (COND ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
         (CONSTRUCT-INITIAL-INTEREST-LINK
           SUPPORTING-NODES
           INSTANTIATIONS
           REASON
           INTEREST
           DEPTH
           PRIORITY
           BINDING
           SUPPOSITION
           :GENERATING-NODE
           GENERATING-NODE
           :REMAINING-PREMISES
           (BACKWARDS-PREMISES REASON)
           :CLUES
           CLUES))
        ((OR (NUMBERP (REASON-STRENGTH REASON))
             (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
                 (DEGREE-OF-INTEREST INTEREST)))
         (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
           (DRAW-CONCLUSION
             (CAR P)
             SUPPORTING-NODES
             REASON
             INSTANTIATIONS
             (DISCOUNT-FACTOR REASON)
             DEPTH
             NIL
             (CDR P)
             :BINDING
             BINDING
             :CLUES
             CLUES)))))

==============================================
Definition overwritten 8/25/2017     14:5:58
--------------------------------------------------------------------------------
(DEFUN MAKE-BACKWARDS-INFERENCE (REASON BINDING INTEREST DEPTH PRIORITY
                                 SUPPORTING-NODES CLUES INSTANTIATIONS
                                 SUPPOSITION &OPTIONAL GENERATING-NODE)
  (COND ((OR (BACKWARDS-PREMISES REASON) (BACKWARDS-PREMISES-FUNCTION REASON))
         (CONSTRUCT-INITIAL-INTEREST-LINK
           SUPPORTING-NODES
           INSTANTIATIONS
           REASON
           INTEREST
           DEPTH
           PRIORITY
           BINDING
           SUPPOSITION
           :GENERATING-NODE
           GENERATING-NODE
           :REMAINING-PREMISES
           (BACKWARDS-PREMISES REASON)
           :CLUES
           CLUES))
        ((OR (NUMBERP (REASON-STRENGTH REASON))
             (>= (FUNCALL (REASON-STRENGTH REASON) BINDING SUPPORTING-NODES)
                 (DEGREE-OF-INTEREST INTEREST)))
         (DOLIST (P (FUNCALL (CONCLUSIONS-FUNCTION REASON) BINDING))
           (DRAW-CONCLUSION
             (CAR P)
             SUPPORTING-NODES
             REASON
             INSTANTIATIONS
             (DISCOUNT-FACTOR REASON)
             DEPTH
             NIL
             (CDR P)
             :BINDING
             BINDING
             :CLUES
             CLUES)))))

==============================================
Definition overwritten 8/25/2017     14:6:5
--------------------------------------------------------------------------------
(DEFUN FLASH-TERMINAL-DEDUCTIVE-ANCESTORS (SELECTED-NODE WIND)
  (FLASH-NODES (SUBSET #'(LAMBDA (N) (ASSOC N (NODE-LIST WIND)))
                       (COMPUTE-TERMINAL-DEDUCTIVE-ANCESTORS SELECTED-NODE))
               WIND
               *BLUE-COLOR*
               5
               (CAT-LIST (LIST "Node "
                               (WRITE-TO-STRING
                                 (INFERENCE-NUMBER SELECTED-NODE))
                               " has no terminal-deductive-ancestors")))
  (WHEN (NOT (SHIFT-KEY-P)) (SETF *FLASH-TERMINAL-DEDUCTIVE-ANCESTORS* NIL)))
