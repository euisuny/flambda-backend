let [@ocamlformat "disable"] print_header () =
  Format.printf
{|; Generated automatically by this directory's dune.
; Run inc.sh to generate a new .inc file.

(alias (name regen))
|}


let [@ocamlformat "disable"] print_test_rule ~compiler ~file =
  Format.printf
{|
(rule
  (alias runtest)
  (enabled_if (= %%{context_name} "main"))
  (deps %s.ml %s.mli)
  (action
   (progn
   (run %s -c -validate %s.mli %s.ml))))
|}
    file file compiler file file

let _ =
  let list_files = Sys.readdir "./" in
  let ml_files =
    List.filter_map (fun x ->
      if    (not (String.equal x "script.ml"))
         && (String.equal (Filename.extension x) ".ml") then
        Some (Filename.remove_extension x)
      else
        None
    )
      (Array.to_list list_files)
  in
  let run basename =
    print_test_rule ~compiler:"%{bin:ocamlopt.opt}" ~file:basename
  in
  print_header ();
  List.map run ml_files
