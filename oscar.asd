;;;; OSCAR system definitions

(in-package :asdf)

(defsystem oscar
    :name "The OSCAR Project"
    :author "John L. Pollock"
    :maintainer "Chun Tian (binghe)"
    :version "4.2"
    :description "The general-purpose defeasible reasoner and architecture for a rational agent"
    :depends-on ()
    :serial t
    :components ((:file "package")
		 (:file "tools")
		 (:file "syntax")
		 (:file "agent-arguments")
		 (:file "base")
		 (:file "assignment-trees")
		 (:file "oscar-core")
		 (:file "reason-macros")
		 (:file "prob-compiler")
		 #+MCL
		 (:file "mcl-graphics")))
