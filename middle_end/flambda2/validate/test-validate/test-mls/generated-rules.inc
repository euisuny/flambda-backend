; Generated automatically by this directory's dune.
; Run inc.sh to generate a new .inc file.

(alias (name regen))

(rule
  (alias runtest)
  (enabled_if (= %{context_name} "main"))
  (deps array1.ml array1.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -c -validate array1.mli array1.ml))))

(rule
  (alias runtest)
  (enabled_if (= %{context_name} "main"))
  (deps test1.ml test1.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -c -validate test1.mli test1.ml))))

(rule
  (alias runtest)
  (enabled_if (= %{context_name} "main"))
  (deps test2.ml test2.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -c -validate test2.mli test2.ml))))

(rule
  (alias runtest)
  (enabled_if (= %{context_name} "main"))
  (deps test3.ml test3.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -c -validate test3.mli test3.ml))))

(rule
  (alias runtest)
  (enabled_if (= %{context_name} "main"))
  (deps cse.ml cse.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -c -validate cse.mli cse.ml))))
