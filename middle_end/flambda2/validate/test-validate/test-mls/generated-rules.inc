; Generated automatically by this directory's dune.
; Run inc.sh to generate a new .inc file.

(alias (name regen))

(rule
 (alias runtest)
  (deps test1.ml test1.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -validate test1.mli test1.ml))))

(rule
 (alias runtest)
  (deps test2.ml test2.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -validate test2.mli test2.ml))))
