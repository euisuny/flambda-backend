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

(rule
  (alias runtest)
  (enabled_if (= %{context_name} "main"))
  (deps region_elim.ml region_elim.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -c -validate region_elim.mli region_elim.ml))))

(rule
  (alias runtest)
  (enabled_if (= %{context_name} "main"))
  (deps project_closure.ml project_closure.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -c -validate project_closure.mli project_closure.ml))))

(rule
  (alias runtest)
  (enabled_if (= %{context_name} "main"))
  (deps box_ints.ml box_ints.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -c -validate box_ints.mli box_ints.ml))))

(rule
  (alias runtest)
  (enabled_if (= %{context_name} "main"))
  (deps tag_imm.ml tag_imm.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -c -validate tag_imm.mli tag_imm.ml))))

(rule
  (alias runtest)
  (enabled_if (= %{context_name} "main"))
  (deps subst_local_alloc.ml subst_local_alloc.mli)
  (action
   (progn
   (run %{bin:ocamlopt.opt} -c -validate subst_local_alloc.mli subst_local_alloc.ml))))
