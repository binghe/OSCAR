(in-package :asdf)

(defsystem oscar
    :name "The OSCAR Project"
    :author "John L. Pollock"
    :maintainer "Chun Tian (binghe)"
    :version "4.1"
    :description "The general-purpose defeasible reasoner and architecture for a rational agent"
    :depends-on ()
    :serial t
    :components ((:file "package")
		 (:file "OSCAR-TOOLS")
		 (:file "Syntax_3")
		 (:file "Agent-arguments5")
		 (:file "base")
		 (:file "Assignment-trees_3-26")
		 (:file "OSCAR_3-31")
		 #+MCL
		 (:file "oscar-graphics17")
		 (:file "Reason-macros_3-31")
		 (:file "Prob-compiler_3-24")
		 (:file "Rules_3-30")
		 ))
