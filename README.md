---
author: John L. Pollock
maintainer: Chun Tian (binghe)
---

# The OSCAR Project

Official website: http://johnpollock.us/ftp/OSCAR-web-page/oscar.html

## Original development platform
- Macintosh Common Lisp 4.2 (on PPC/Mac OS X)

## Common Lisp platforms confirmed working
- Macintosh Common Lisp (RMCL) 5.2, 6.0
- LispWorks 6.1, 7.0, 7.1 (*version <= 6.0 doesn't work!*)
- CMU Common Lisp 21b
- SBCL 1.3.19
- Clozure CL 1.11

## To load OSCAR (using ASDF)
- Add OSCAR's directory into ASDF's *central-registry*
- Start Common Lisp REPL
- Run the following command :
`(asdf:load-system :oscar)`

NOTE: if you're also using MCL, before calling ASDF please change the value of `oscar-pathname` at the end of `package.lisp` to your absolute path of OSCAR home pathname, in Mac OS 9 classic format.

### Why isn't OSCAR included in Quicklisp?

```
"This license is too restrictive for inclusion in Quicklisp, sorry." -- Zach Beane, August 28, 2017
```

see <https://github.com/quicklisp/quicklisp-projects/issues/1378#issuecomment-325326234> for details.

## To run OSCAR's graphics interface in MCL
- Change current Lisp package to OSCAR: `(in-package :oscar)`
- Run `(initialize-graphics)`

## How to run tests
- Manually load 2 more Lisp files (in same order as below) without compilation:
 1. Execute `(load #p"OSCAR:rules.lisp")`,
 2. Execute `(load #p"OSCAR:combined-problems.lisp")`,
- Change current Lisp package to OSCAR
- Execute `(oscar:test n)` (`n` is the problem number, 1-104) or just `(oscar:test)`

## How to run simulations (untested)
- Execute `(load #p"OSCAR:perception-causes.lisp")`
- Execute `(load #p"OSCAR:pc-examples.lisp")`
