---
author: John L. Pollock
maintainer: Chun Tian (binghe)
---

# The OSCAR Project

Official website: http://johnpollock.us/ftp/OSCAR-web-page/oscar.html

## Original development platform
- Macintosh Common Lisp 4.2 (on PPC/Mac OS X)

## Common Lisp platforms confirmed working
- Rosetta Macintosh Common Lisp (RMCL) 6.0 (on Intel/Mac OS X 10.6)
- LispWorks 7.0 (all platforms)

## To load OSCAR (using ASDF)
- Add OSCAR's directory into ASDF's *central-registry*
- Start Common Lisp REPL
- Run the following command :
`(asdf:load-system :oscar)`

NOTE: if you're also using MCL, before calling ASDF please change the value of `oscar-pathname` at the end of `package.lisp` to your absolute path of OSCAR home pathname, in Mac OS 9 classic format.

## To run OSCAR's graphics interface on MCL
- Change current Lisp package to OSCAR: `(in-package :oscar)` or `(in-package "OSCAR")`
- Run `(initialize-graphics)`

## How to run tests
- Manually load 3 more Lisp files (in same order as below) without compilation:
 1. Run `(load "Rules_3-30.lisp")`,
 2. Run `(load "Combined-problems.lisp")`,
 3. Run `(load "Agent-arguments5.lisp")`
- Change current Lisp package to OSCAR: `(in-package :oscar)` or `(in-package "OSCAR")`
- Run `(test n)` or just `(test)`

## How to run simulations
- Run `(load "Perception-Causes_3-31.lisp")`
- Run `(load "PC-examples_3-31.lisp")`
