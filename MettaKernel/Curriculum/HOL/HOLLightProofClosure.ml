(* Export the finite ProofTrace closure of a selected HOL Light theorem.

   This file runs only with the checked-in ProofTrace kernel patch applied.
   The emitted JSON-lines files are an untrusted source artifact: MIK must
   independently validate their rule applications and theorem results. *)

#use "ProofTrace/proofs.ml";;

let proof_children proof =
  let Proof(_,_,content) = proof in
  match content with
    Prefl _ | Pbeta _ | Passume _ | Paxiom _ | Pdef _ -> []
  | Ptrans(left,right)
  | Pmkcomb(left,right)
  | Peqmp(left,right)
  | Pdeduct(left,right) -> [left;right]
  | Pabs(parent,_)
  | Pinst(parent,_)
  | Pinstt(parent,_)
  | Pdeft(parent,_,_,_) -> [parent];;

let proof_closure root =
  let seen = Hashtbl.create 257 in
  let rec visit proof =
    let index = proof_index proof in
    if not (Hashtbl.mem seen index) then begin
      Hashtbl.add seen index proof;
      List.iter visit (proof_children proof)
    end in
  visit root;
  Hashtbl.fold (fun _ proof acc -> proof :: acc) seen []
  |> List.sort (fun left right -> proof_index left - proof_index right);;

let write_lines filename render values =
  let channel = open_out filename in
  List.iter
    (fun value -> Printf.fprintf channel "%s\n" (render value))
    values;
  flush channel;
  close_out channel;;

let dump_proof_closure prefix theorem_name theorem =
  let root = proof_of theorem in
  let closure = proof_closure root in
  write_lines (prefix ^ ".proofs") proof_string closure;
  write_lines (prefix ^ ".theorems") theorem_string closure;
  let names = open_out (prefix ^ ".names") in
  Printf.fprintf names
    "{\"id\": %d, \"nm\": \"%s\"}\n"
    (proof_index root) (String.escaped theorem_name);
  flush names;
  close_out names;
  Printf.printf
    "HOL_LIGHT_PROOF_CLOSURE_OK theorem=%s root=%d nodes=%d\n"
    theorem_name (proof_index root) (List.length closure);;

(* Structured source export avoids the compact printer's delimiter ambiguity.
   It retains the source substitution list in its original order. *)
let hol_json_string text =
  let buffer = Buffer.create (String.length text + 2) in
  Buffer.add_char buffer '"';
  String.iter (fun character ->
    match character with
      '"' -> Buffer.add_string buffer "\\\""
    | '\\' -> Buffer.add_string buffer "\\\\"
    | c when Char.code c < 32 || Char.code c >= 128 ->
        Printf.bprintf buffer "\\u%04x" (Char.code c)
    | c -> Buffer.add_char buffer c) text;
  Buffer.add_char buffer '"';
  Buffer.contents buffer;;

let hol_json_list render values =
  "[" ^ String.concat "," (List.map render values) ^ "]";;

let rec hol_type_json = function
    Tyvar name -> "[\"var\"," ^ hol_json_string name ^ "]"
  | Tyapp(name,arguments) ->
      "[\"op\"," ^ hol_json_string name ^ "," ^ hol_json_list hol_type_json arguments ^ "]";;

let rec hol_term_json = function
    Var(name,ty) -> "[\"var\"," ^ hol_json_string name ^ "," ^ hol_type_json ty ^ "]"
  | Const(name,ty) -> "[\"const\"," ^ hol_json_string name ^ "," ^ hol_type_json ty ^ "]"
  | Comb(function_term,argument) ->
      "[\"app\"," ^ hol_term_json function_term ^ "," ^ hol_term_json argument ^ "]"
  | Abs(variable,body) -> "[\"abs\"," ^ hol_term_json variable ^ "," ^ hol_term_json body ^ "]";;

let hol_theorem_json theorem =
  "{\"hypotheses\":" ^ hol_json_list hol_term_json (hyp theorem) ^
  ",\"conclusion\":" ^ hol_term_json (concl theorem) ^ "}";;

let hol_proof_json proof =
  let Proof(index,theorem,content) = proof in
  let reference child = string_of_int (proof_index child) in
  let pair render (replacement,variable) =
    "[" ^ render replacement ^ "," ^ render variable ^ "]" in
  let rule,arguments = match content with
      Prefl term -> "REFL", [hol_term_json term]
    | Ptrans(left,right) -> "TRANS", [reference left;reference right]
    | Pmkcomb(left,right) -> "MK_COMB", [reference left;reference right]
    | Pabs(parent,variable) -> "ABS", [reference parent;hol_term_json variable]
    | Pbeta term -> "BETA", [hol_term_json term]
    | Passume term -> "ASSUME", [hol_term_json term]
    | Peqmp(left,right) -> "EQ_MP", [reference left;reference right]
    | Pdeduct(left,right) -> "DEDUCT_ANTISYM_RULE", [reference left;reference right]
    | Pinst(parent,entries) -> "INST", [reference parent;hol_json_list (pair hol_term_json) entries]
    | Pinstt(parent,entries) -> "INST_TYPE", [reference parent;hol_json_list (pair hol_type_json) entries]
    | Paxiom term -> "AXIOM", [hol_term_json term]
    | Pdef(term,name,ty) -> "DEFINITION", [hol_term_json term;hol_json_string name;hol_type_json ty]
    | Pdeft(parent,term,name,ty) ->
        "TYPE_DEFINITION", [reference parent;hol_term_json term;hol_json_string name;hol_type_json ty] in
  "{\"id\":" ^ string_of_int index ^ ",\"rule\":" ^ hol_json_string rule ^
  ",\"arguments\":" ^ hol_json_list (fun text -> text) arguments ^
  ",\"theorem\":" ^ hol_theorem_json theorem ^ "}";;

(* Declarations can be dependencies even when no inference uses their
   defining theorem. Follow references in types and terms as well as premises. *)
let hol_light_live_closure named_theorems =
  let seen = Hashtbl.create 257 in
  let used_types = Hashtbl.create 31 and used_constants = Hashtbl.create 127 in
  let constant_definitions = Hashtbl.create 127 and type_groups = Hashtbl.create 31 in
  List.iter (fun theorem ->
    let proof = proof_of theorem in
    let Proof(_,_,content) = proof in
    match content with
      Pdef(_,name,_) -> Hashtbl.add constant_definitions name proof
    | _ -> failwith "HOLLightProofClosure: definition registry") (definitions());
  let type_definitions = List.filter (fun proof ->
    let Proof(_,_,content) = proof in
    match content with Pdeft _ -> true | _ -> false) (proofs()) in
  List.iter (fun proof ->
    let Proof(_,_,content) = proof in
    match content with
      Pdeft(_,equation,_,ty) ->
        let _,right = dest_eq equation in
        let abstract_type = if is_var right then type_of right else fst(dest_fun_ty ty) in
        let name,_ = dest_type abstract_type in
        let previous = try Hashtbl.find type_groups name with Not_found -> [] in
        Hashtbl.replace type_groups name (proof :: previous)
    | _ -> failwith "HOLLightProofClosure: type-definition registry") type_definitions;
  let rec visit_type = function
      Tyvar _ -> ()
    | Tyapp(name,arguments) ->
        if not(Hashtbl.mem used_types name) then begin
          Hashtbl.add used_types name ();
          (try List.iter visit_proof (Hashtbl.find type_groups name) with Not_found -> ())
        end;
        List.iter visit_type arguments
  and visit_term = function
      Var(_,ty) -> visit_type ty
    | Const(name,ty) ->
        visit_type ty;
        if not(Hashtbl.mem used_constants name) then begin
          Hashtbl.add used_constants name ();
          visit_type (get_const_type name);
          (try visit_proof (Hashtbl.find constant_definitions name) with Not_found -> ())
        end
    | Comb(function_term,argument) -> visit_term function_term; visit_term argument
    | Abs(variable,body) -> visit_term variable; visit_term body
  and visit_proof proof =
    let Proof(index,theorem,content) = proof in
    if not(Hashtbl.mem seen index) then begin
      Hashtbl.add seen index proof;
      List.iter visit_proof (proof_children proof);
      List.iter visit_term (concl theorem :: hyp theorem);
      match content with
        Prefl term | Pbeta term | Passume term | Paxiom term -> visit_term term
      | Pabs(_,variable) -> visit_term variable
      | Pinst(_,entries) -> List.iter (fun (term,variable) -> visit_term term; visit_term variable) entries
      | Pinstt(_,entries) -> List.iter (fun (ty,key) -> visit_type ty; visit_type key) entries
      | Pdef(term,_,ty) | Pdeft(_,term,_,ty) -> visit_term term; visit_type ty
      | Ptrans _ | Pmkcomb _ | Peqmp _ | Pdeduct _ -> ()
    end in
  List.iter (fun (_,theorem) -> visit_proof (proof_of theorem)) named_theorems;
  let closure = Hashtbl.fold (fun _ proof values -> proof :: values) seen [] in
  (List.sort (fun left right -> compare (proof_index left) (proof_index right)) closure,
   List.filter (fun (name,_) -> Hashtbl.mem used_types name) (types()),
   List.filter (fun (name,_) -> Hashtbl.mem used_constants name) (constants()));;

let dump_structured_proof_closures prefix named_theorems =
  let closure,signature_types,signature_constants = hol_light_live_closure named_theorems in
  let declaration_roots = List.filter (fun proof ->
    let Proof(_,_,content) = proof in
    match content with Pdef _ | Pdeft _ -> true | _ -> false) closure in
  let axiom_roots = List.filter (fun proof ->
    let Proof(_,_,content) = proof in
    match content with Paxiom _ -> true | _ -> false) closure in
  write_lines (prefix ^ ".nodes.jsonl") hol_proof_json closure;
  write_lines (prefix ^ ".roots.jsonl")
    (fun (name,theorem) ->
      "{\"name\":" ^ hol_json_string name ^ ",\"id\":" ^
      string_of_int (proof_index (proof_of theorem)) ^ "}") named_theorems;
  write_lines (prefix ^ ".signature.json") (fun text -> text)
    ["{\"types\":" ^ hol_json_list
       (fun (name,arity) -> "[" ^ hol_json_string name ^ "," ^ string_of_int arity ^ "]")
       signature_types ^ ",\"constants\":" ^ hol_json_list
       (fun (name,ty) -> "[" ^ hol_json_string name ^ "," ^ hol_type_json ty ^ "]")
       signature_constants ^ ",\"definition_roots\":" ^ hol_json_list
       (fun proof -> string_of_int (proof_index proof))
       declaration_roots ^
       ",\"axiom_roots\":" ^ hol_json_list
       (fun proof -> string_of_int (proof_index proof)) axiom_roots ^ "}"];
  Printf.printf "HOL_LIGHT_STRUCTURED_CLOSURE_OK roots=%d nodes=%d\n"
    (List.length named_theorems) (List.length closure);;

let hol_export_library_only =
  try Sys.getenv "MIK_HOL_LIGHT_LIBRARY_ONLY" = "1" with Not_found -> false;;

if not hol_export_library_only then begin
  let output_prefix =
    try Sys.getenv "MIK_HOL_LIGHT_TRACE_PREFIX"
    with Not_found -> "ProofTrace/mik_self_imp" in
  let p = `p:bool` in
  let self_imp = DISCH p (ASSUME p) in
  if not (aconv (concl self_imp) (mk_imp(p,p))) then
    failwith "HOLLightProofClosure: SELF_IMP conclusion";
  if hyp self_imp <> [] then
    failwith "HOLLightProofClosure: SELF_IMP hypotheses";
  dump_proof_closure output_prefix "SELF_IMP" self_imp;
  exit 0
end;;
