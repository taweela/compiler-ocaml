#use "tp_sa.ml"
let file_to_string input_file =
  let in_channel = open_in input_file in
  let rec run () =
    try 
      let ch = input_char in_channel in ch :: (run ())
    with End_of_file ->
      ( close_in in_channel;
	[] )
  in string_of_list (run ());;

let string_to_file output_file out_string =
  let out_channel = open_out output_file in
  ( output_string out_channel out_string;
    close_out out_channel );;

module type CODE_GENERATION =sig
    val compile_scheme_string : string -> string -> unit
    val compile_scheme_file : string -> string -> unit
  end;;

module Code_Generation (*: CODE_GENERATION*)= struct


  (* areas that raise this exception are NOT for the
   * final project! please leave these unimplemented,
   * as this will require major additions to your
   * compilers
   *)
  exception X_not_yet_supported;;

  let word_size = 8;;
  let label_start_of_constants_table = "L_constants";;
  let comment_length = 20;;
  let empty_list=[];;
  let offset_Fbool=2;;
  let offset_Tbool=3;;
  
  let offset_void=0;;
  let offset_Nil=1;;
  let offset_char=4;;

  let list_and_last =
    let rec run a = function
      | [] -> ([], a)
      | b :: s ->
         let (s, last) = run b s in
         (a :: s, last)
    in function
    | [] -> None
    | a :: s -> Some (run a s);;

  let split_to_sublists n = 
    let rec run = function
      | ([], _, f) -> [f []]
      | (s, 0, f) -> (f []) :: (run (s, n, (fun s -> s)))
      | (a :: s, i, f) ->
         (run (s, i - 1, (fun s -> f (a :: s))))
    in function
    | [] -> []
    | s -> run (s, n, (fun s -> s));;
  let check_do lis lis2=
  
    if (not (List.mem lis lis2))
      then lis2 @ [lis]
  else lis2;;  
  let remove_duplicates = (*raise X_not_yet_implemented;;*)
  let r_dupList list = List.fold_left (fun lis2 lis -> 
    check_do lis lis2)
     [] list in fun list -> r_dupList list;;







  let collect_constants = (*raise X_not_yet_implemented;;*)(*collect the cons and sub cons return list of con and sub cons *)
  let rec run = function 
  | ScmConst' e -> [e]
  | ScmVarGet' _ -> empty_list
  | ScmBox' _ -> empty_list
  | ScmBoxGet' _ -> empty_list
  | ScmVarSet' (_, e) -> run e 
  | ScmVarDef' (_, e) -> run e 
  | ScmBoxSet' (_, e) -> run e
  | ScmIf' (test, dit, dif ) ->  List.append(List.append (run test)(run dit))(run dif)
  | ScmOr' listOfExpsOr -> run_list listOfExpsOr
  | ScmSeq' listOfExpsSeq -> run_list listOfExpsSeq
  | ScmLambda' (_, _, e) -> run e
  | ScmApplic' (e, exprs, _) -> run e @ run_list exprs

  and run_list listOfExprs = 
    List.fold_left
    (fun v e -> v @ (run e)) empty_list listOfExprs
    in 
    fun listOfExprs -> run_list listOfExprs;; 


  let add_sub_constants = 
    (*add the sub first to the table without dup, () added once*)
    let rec run sexpr = match sexpr with
      | ScmVoid -> (*raise X_not_yet_implemented*)
          (*there is no const and we return []*) [sexpr]

      | ScmNil -> (*raise X_not_yet_implemented*)
           (*there is no const and we return []*) [sexpr]

      | ScmBoolean _ | ScmChar _ | ScmString _ | ScmNumber _ ->
        (* raise X_not_yet_implemented*)
        (*this is scmConst*) 
        [sexpr]

      | ScmSymbol sym -> (*raise X_not_yet_implemented*)
      (*if we have symbol we return the string of this symbol and his address *)
        [ScmString(sym);ScmSymbol sym] (*the bug was here , added the scmsym to the list *)

      | ScmPair (car, cdr) -> (run car) @ (run cdr) @ [sexpr]

      | ScmVector sexprs -> (*raise X_not_yet_implemented*)
      (*`(,@ (map runs (vactor->list sexpr)),@sexpr) in lecture we convert scheme to ocaml *)
        List.append(runs sexprs) [sexpr]

        
    and runs sexprs =
      List.fold_left (fun full sexpr -> full @ (run sexpr)) [] sexprs
    in fun exprs' ->
       [ScmVoid; ScmNil; ScmBoolean false; ScmBoolean true; ScmChar '\000'] @ (runs exprs');;

  type initialized_data =
    | RTTI of string
    | Byte of int
    | ASCII of string
    | Quad of int
    | QuadFloat of float
    | ConstPtr of int;;
  let check_if_empty sym table=
  if( table== [] )
    then  raise (X_this_should_not_happen
  (Printf.sprintf
     "The variable %s was not found in the constants table"
     (string_of_sexpr sym)));;
  let search_constant_address = (*raise X_not_yet_implemented;;*)

  let rec find_constant_add constants_s const_table  = match const_table with

           (*IF the constant table a empty list we shuold throw an exception*)
                             
    | [] ->  raise (X_this_should_not_happen
      (Printf.sprintf
         "in this constant table there is no %s "
         (string_of_sexpr constants_s)))                              
    (* | first :: rest -> let (cur_exp,location,repr)=first in 
      if(cur_exp==constants_s) then(location) else (find_constant_add constants_s rest) *)  (*the bug of const tests was here*)
      (*from the lecture of Mayeer*)
    | (cur_exp,location,_repr):: rest when constants_s=cur_exp -> location

    | _::  rest -> find_constant_add constants_s rest                             

      


in fun constants_s const_table ->
  match constants_s with
  | ScmBoolean false -> offset_Fbool
  | ScmBoolean true -> offset_Tbool
  | ScmVoid -> offset_void
  | ScmNil -> offset_Nil
  | ScmChar '\000' -> offset_char
  | _ -> (find_constant_add constants_s const_table);;


  let const_repr sexpr loc table = match sexpr with
    | ScmVoid -> ([RTTI "T_void"], 1)
    | ScmNil -> ([RTTI "T_nil"], 1)
    | ScmBoolean false ->
       ([RTTI "T_boolean_false"], 1)
    | ScmBoolean true ->
       ([RTTI "T_boolean_true"], 1)
    | ScmChar ch ->
       ([RTTI "T_char"; Byte (int_of_char ch)], 2)
    | ScmString str ->
       let count = String.length str in
       ([RTTI "T_string"; Quad count; ASCII str],
        1 + word_size + count)
    | ScmSymbol sym ->
       let addr = search_constant_address (ScmString sym) table in
       ([RTTI "T_symbol"; ConstPtr addr], 1 + word_size)
    | ScmNumber (ScmRational (numerator, denominator)) ->
       ([RTTI "T_rational"; Quad numerator; Quad denominator],
        1 + 2 * word_size)
    | ScmNumber (ScmReal x) ->
       ([RTTI "T_real"; QuadFloat x], 1 + word_size)
    | ScmVector s ->
       let addrs =
         List.map
           (fun si -> ConstPtr (search_constant_address si table)) s in
       let count = List.length s in
       ((RTTI "T_vector") :: (Quad count) :: addrs,
        1 + (count + 1) * word_size)
    | ScmPair (car, cdr) ->
       let (addr_car, addr_cdr) =
         (search_constant_address car table,
          search_constant_address cdr table) in
       ([RTTI "T_pair"; ConstPtr addr_car; ConstPtr addr_cdr],
        1 + 2 * word_size);;

  let make_constants_table =
    let rec run table loc = function
      | [] -> table
      | sexpr :: sexprs ->
         let (repr, len) = const_repr sexpr loc table in
         run (table @ [(sexpr, loc, repr)]) (loc + len) sexprs
    in
    fun exprs' ->
    run [] 0
      (remove_duplicates
         (add_sub_constants
            (remove_duplicates
               (collect_constants exprs'))));;    

  let asm_comment_of_sexpr sexpr =
    let str = string_of_sexpr sexpr in
    let str =
      if (String.length str) <= comment_length
      then str
      else (String.sub str 0 comment_length) ^ "..." in
    "; " ^ str;;

  let asm_of_representation sexpr =
    let str = asm_comment_of_sexpr sexpr in
    let run = function
      | [RTTI str] -> Printf.sprintf "\tdb %s" str
      | [RTTI "T_char"; Byte byte] ->
         Printf.sprintf "\tdb T_char, 0x%02X\t%s" byte str
      | [RTTI "T_string"; Quad length; ASCII const_str] ->
         Printf.sprintf "\tdb T_string\t%s\n\tdq %d%s"
           str length
           (let s = list_of_string const_str in
            let s = List.map
                      (fun ch -> Printf.sprintf "0x%02X" (int_of_char ch))
                      s in
            let s = split_to_sublists 8 s in
            let s = List.map (fun si -> "\n\tdb " ^ (String.concat ", " si)) s in
            String.concat "" s)
      | [RTTI "T_symbol"; ConstPtr addr] ->
         Printf.sprintf "\tdb T_symbol\t%s\n\tdq %s + %d"
           str label_start_of_constants_table addr
      | [RTTI "T_rational"; Quad numerator; Quad denominator] ->
         Printf.sprintf "\tdb T_rational\t%s\n\tdq %d, %d"
           str
           numerator denominator
      | [RTTI "T_real"; QuadFloat x] ->
         Printf.sprintf "\tdb T_real\t%s\n\tdq %f" str x
      | (RTTI "T_vector") :: (Quad length) :: addrs ->
         Printf.sprintf "\tdb T_vector\t%s\n\tdq %d%s"
           str length
           (let s = List.map
                      (function
                       | ConstPtr ptr ->
                          Printf.sprintf "%s + %d"
                            label_start_of_constants_table ptr
                       | _ -> raise
                               (X_this_should_not_happen
                                  "incorrect representation for a vector"))
                      addrs in
            let s = split_to_sublists 3 s in
            let s = List.map (fun si -> "\n\tdq " ^ (String.concat ", " si)) s in
            String.concat "" s)
      | [RTTI "T_pair"; ConstPtr car; ConstPtr cdr] ->
         Printf.sprintf "\tdb T_pair\t%s\n\tdq %s + %d, %s + %d"
           str
           label_start_of_constants_table car
           label_start_of_constants_table cdr
      | _ -> raise (X_this_should_not_happen "invalid representation!")
    in run;;

  let asm_of_constants_table =
    let rec run = function
      | [] -> ""
      | (sexpr, _, repr) :: rest ->
         (asm_of_representation sexpr repr) ^ "\n" ^ (run rest)
    in
    fun table ->
    Printf.sprintf "%s:\n%s"
      label_start_of_constants_table (run table);;

  let global_bindings_table =
    [ (* 1-10 *)
      ("null?", "L_code_ptr_is_null");
      ("pair?", "L_code_ptr_is_pair");
      ("void?", "L_code_ptr_is_void");
      ("char?", "L_code_ptr_is_char");
      ("string?", "L_code_ptr_is_string");
      ("symbol?", "L_code_ptr_is_symbol");
      ("vector?", "L_code_ptr_is_vector");
      ("procedure?", "L_code_ptr_is_closure");
      ("real?", "L_code_ptr_is_real");
      ("rational?", "L_code_ptr_is_rational");
      ("boolean?", "L_code_ptr_is_boolean");
      (* 11-20 *)
      ("number?", "L_code_ptr_is_number");
      ("collection?", "L_code_ptr_is_collection");
      ("cons", "L_code_ptr_cons");
      ("display-sexpr", "L_code_ptr_display_sexpr");
      ("write-char", "L_code_ptr_write_char");
      ("car", "L_code_ptr_car");
      ("cdr", "L_code_ptr_cdr");
      ("string-length", "L_code_ptr_string_length");
      ("vector-length", "L_code_ptr_vector_length");
      ("real->integer", "L_code_ptr_real_to_integer");
      (* 21-30*)
      ("exit", "L_code_ptr_exit");
      ("integer->real", "L_code_ptr_integer_to_real");
      ("rational->real", "L_code_ptr_rational_to_real");
      ("char->integer", "L_code_ptr_char_to_integer");
      ("integer->char", "L_code_ptr_integer_to_char");
      ("trng", "L_code_ptr_trng");
      ("zero?", "L_code_ptr_is_zero");
      ("integer?", "L_code_ptr_is_integer");
      ("__bin-apply", "L_code_ptr_bin_apply");
      ("__bin-add-rr", "L_code_ptr_raw_bin_add_rr");
      (* 31-40*)
      ("__bin-sub-rr", "L_code_ptr_raw_bin_sub_rr");
      ("__bin-mul-rr", "L_code_ptr_raw_bin_mul_rr");
      ("__bin-div-rr", "L_code_ptr_raw_bin_div_rr");
      ("__bin-add-qq", "L_code_ptr_raw_bin_add_qq");
      ("__bin-sub-qq", "L_code_ptr_raw_bin_sub_qq");
      ("__bin-mul-qq", "L_code_ptr_raw_bin_mul_qq");
      ("__bin-div-qq", "L_code_ptr_raw_bin_div_qq");
      ("error", "L_code_ptr_error");
      ("__bin-less-than-rr", "L_code_ptr_raw_less_than_rr");
      ("__bin-less-than-qq", "L_code_ptr_raw_less_than_qq");
      (* 41-50 *)
      ("__bin-equal-rr", "L_code_ptr_raw_equal_rr");
      ("__bin-equal-qq", "L_code_ptr_raw_equal_qq");
      ("quotient", "L_code_ptr_quotient");
      ("remainder", "L_code_ptr_remainder");
      ("set-car!", "L_code_ptr_set_car");
      ("set-cdr!", "L_code_ptr_set_cdr");
      ("string-ref", "L_code_ptr_string_ref");
      ("vector-ref", "L_code_ptr_vector_ref");
      ("vector-set!", "L_code_ptr_vector_set");
      ("string-set!", "L_code_ptr_string_set");
      (* 51-60 *)
      ("make-vector", "L_code_ptr_make_vector");
      ("make-string", "L_code_ptr_make_string");
      ("numerator", "L_code_ptr_numerator");
      ("denominator", "L_code_ptr_denominator");
      ("eq?", "L_code_ptr_eq")
    ];;

  let collect_free_vars =
    let rec run = function
      | ScmConst' _ -> (*raise X_not_yet_implemented*)
          empty_list

      | ScmVarGet' (Var' (v, Free)) -> [v]

      | ScmVarGet' _ -> (*raise X_not_yet_implemented*)
        empty_list  

      | ScmIf' (test, dit, dif) -> (*raise X_not_yet_implemented*)
            (*take the free vars from test , dit and dif and append the to list*)
            List.append(List.append (run test)(run dit))(run dif)

      | ScmSeq' exprs' -> runs exprs'
      | ScmOr' exprs' -> runs exprs'

      | ScmVarSet' (Var' (v, Free), expr') -> (*raise X_not_yet_implemented*)
            (*take the var and run all over the expr' in rec return list of appending v with the free vars in expr' *)
              List.append [v] (run expr') 

      | ScmVarSet' (_, expr') -> (*raise X_not_yet_implemented*)
          run expr'

      | ScmVarDef' (Var' (v, Free), expr') -> (*raise X_not_yet_implemented*) (*the same as ScmVarSet*)
        List.append [v] (run expr') 

      | ScmVarDef' (_, expr') -> run expr'
      | ScmBox' (Var' (v, Free)) -> (*raise X_not_yet_implemented*)
             [v]

      | ScmBox' _ -> []
      | ScmBoxGet' (Var' (v, Free)) -> (*raise X_not_yet_implemented*)
        [v]

      | ScmBoxGet' _ -> []
      | ScmBoxSet' (Var' (v, Free), expr') -> (*raise X_not_yet_implemented*)
          List.append [v] (run expr')

      | ScmBoxSet' (_, expr') -> run expr'
      | ScmLambda' (_, _, expr') -> (*raise X_not_yet_implemented*)
         run expr'

      | ScmApplic' (expr', exprs', _) -> (*raise X_not_yet_implemented*)
        List.append (run expr') (runs exprs')


    and runs exprs' =
      List.fold_left
        (fun vars expr' -> vars @ (run expr'))
        []
        exprs'
    in fun exprs' ->
       let primitives =
         List.map
           (fun (scheme_name, _) -> scheme_name)
           global_bindings_table
       and free_vars_in_code = runs exprs' in
       remove_duplicates
         (primitives @ free_vars_in_code);;

  let make_free_vars_table =
    let rec run index = function
      | [] -> []
      | v :: vars ->
         let x86_label = Printf.sprintf "free_var_%d" index in
         (v, x86_label) :: (run (index + 1) vars)
    in fun exprs' -> run 0 (collect_free_vars exprs');;

  let search_free_var_table =
    let rec run v = function
      | [] -> raise (X_this_should_not_happen
                      (Printf.sprintf
                         "The variable %s was not found in the free-var table"
                         v))
      | (v', x86_label) :: _ when v = v' -> x86_label
      | _ :: table -> run v table
    in run;;

  let asm_of_global_bindings global_bindings_table free_var_table =
    String.concat "\n"
      (List.map
         (fun (scheme_name, asm_code_ptr) ->
           let free_var_label =
             search_free_var_table scheme_name free_var_table in
           (Printf.sprintf "\t; building closure for %s\n" scheme_name)
           ^ (Printf.sprintf "\tmov rdi, %s\n" free_var_label)
           ^ (Printf.sprintf "\tmov rsi, %s\n" asm_code_ptr)
           ^ "\tcall bind_primitive\n")
         global_bindings_table);;
  
  let asm_of_free_vars_table table =
    let tmp = 
      List.map
        (fun (scm_var, asm_label) ->
          Printf.sprintf "%s:\t; location of %s\n\tresq 1"
            asm_label scm_var)
        table in
    String.concat "\n" tmp;;

  let make_make_label prefix =
    let index = ref 0 in
    fun () ->
    (index := !index + 1;
     Printf.sprintf "%s_%04x" prefix !index);;

  let make_if_else = make_make_label ".L_if_else";;
  let make_if_end = make_make_label ".L_if_end";;
  let make_or_end = make_make_label ".L_or_end";;
  let make_lambda_simple_loop_env =
    make_make_label ".L_lambda_simple_env_loop";;
  let make_lambda_simple_loop_env_end =
    make_make_label ".L_lambda_simple_env_end";;
  let make_lambda_simple_loop_params =
    make_make_label ".L_lambda_simple_params_loop";;
  let make_lambda_simple_loop_params_end =
    make_make_label ".L_lambda_simple_params_end";;
  let make_lambda_simple_code = make_make_label ".L_lambda_simple_code";;
  let make_lambda_simple_end = make_make_label ".L_lambda_simple_end";;
  let make_lambda_simple_arity_ok =
    make_make_label ".L_lambda_simple_arity_check_ok";;
  let make_lambda_opt_loop_env =
    make_make_label ".L_lambda_opt_env_loop";;
  let make_lambda_opt_loop_env_end =
    make_make_label ".L_lambda_opt_env_end";;
  let make_lambda_opt_loop_params =
    make_make_label ".L_lambda_opt_params_loop";;
  let make_lambda_opt_loop_params_end =
    make_make_label ".L_lambda_opt_params_end";;
  let make_lambda_opt_code = make_make_label ".L_lambda_opt_code";;
  let make_lambda_opt_end = make_make_label ".L_lambda_opt_end";;
  let make_lambda_opt_arity_exact =
    make_make_label ".L_lambda_opt_arity_check_exact";;
  let make_lambda_opt_arity_more =
    make_make_label ".L_lambda_opt_arity_check_more";;
  let make_lambda_opt_stack_ok =
    make_make_label ".L_lambda_opt_stack_adjusted";;
  let make_lambda_opt_loop =
    make_make_label ".L_lambda_opt_stack_shrink_loop";;
  let make_lambda_opt_loop_exit =
    make_make_label ".L_lambda_opt_stack_shrink_loop_exit";;
  let make_tc_applic_recycle_frame_loop =
    make_make_label ".L_tc_recycle_frame_loop";;
  let make_tc_applic_recycle_frame_done =
    make_make_label ".L_tc_recycle_frame_done";;

  let code_gen exprs' =
    let consts = make_constants_table exprs' in
    let free_vars = make_free_vars_table exprs' in
    let rec run params env = function
      | ScmConst' sexpr -> (*raise X_not_yet_implemented*)
        (Printf.sprintf "\tmov rax, L_constants + %d\n" (search_constant_address sexpr consts))

        
      | ScmVarGet' (Var' (v, Free)) ->
         let label = search_free_var_table v free_vars in
         Printf.sprintf
           "\tmov rax,  [%s]\n"
           label
      | ScmVarGet' (Var' (v, Param minor)) -> (*raise X_not_yet_implemented*)
           (Printf.sprintf 
           "\tmov rax,  [rbp +8 * (4 + %s)]\n" 
           (string_of_int(minor)))


      | ScmVarGet' (Var' (v, Bound (major, minor))) ->(*raise X_not_yet_implemented*)
          (*  
          from the lecture of mayeer  
           mov rax,  [rbp + 8 ∗ 2]
                
           mov rax,  [rax + 8 ∗ major]
                
           mov rax,  [rax + 8 ∗ minor]*)

           (Printf.sprintf "mov rax,  [rbp + %d]\n" (8 * 2)) ^
           (Printf.sprintf "mov rax,  [rax + %d]\n" (8 * major)) ^
           (Printf.sprintf "mov rax,  [rax + %d]\n" (8 * minor))


      | ScmIf' (test, dit, dif) -> (*raise X_not_yet_implemented*)
        (*If'(Q, T , E)
          test 
         cmp rax, sob_false
         je Lelse
           dit
         jmp Lexit
         Lelse:
         dif
         Lexit:*)
      let test_As=  run params env test in 
      let else_l = make_if_else() in 
      let end_l = make_if_end() in
      test_As ^
      "\tcmp rax, sob_boolean_false\n" ^
      (Printf.sprintf "\tje %s\n"  else_l) ^
      run params env dit ^
      (Printf.sprintf "\tjmp %s\n" end_l) ^
      (Printf.sprintf "\t%s:\n"  else_l) ^
      "\t" ^
      run params env dif ^
      (Printf.sprintf "\t%s:\n" end_l) 

      | ScmSeq' exprs' ->
         String.concat "\n"
           (List.map (run params env) exprs')
      | ScmOr' exprs' ->
         let label_end = make_or_end () in
         let asm_code = 
           (match (list_and_last exprs') with
            | Some (exprs', last_expr') ->
               let exprs_code =
                 String.concat ""
                   (List.map
                      (fun expr' ->
                        let expr_code = run params env expr' in
                        expr_code
                        ^ "\tcmp rax, sob_boolean_false\n"
                        ^ (Printf.sprintf "\tjne %s\n" label_end))
                      exprs') in
               let last_expr_code = run params env last_expr' in
               exprs_code
               ^ last_expr_code
               ^ (Printf.sprintf "%s:\n" label_end)
            (* and just in case someone messed up the tag-parser: *)
            | None -> run params env (ScmConst' (ScmBoolean false)))
         in asm_code
      | ScmVarSet' (Var' (v, Free), expr') ->
         (* raise X_not_yet_implemented *)

      (*
      Set(Var'(VarFree'(v)),E)expr'
          = [expr']
          mov  [LabelInFVarTable(v)], rax  i have to check that 
          mov rax, sob_void*)
          (run params env expr') ^
          (Printf.sprintf "\tmov  [%s], rax\n" (search_free_var_table v free_vars)) ^
          "\tmov rax, sob_void\n"

      | ScmVarSet' (Var' (v, Param minor), expr') ->
         (* raise X_not_yet_implemented *)
         let run_parms_env=run params env expr' in
         (run_parms_env) ^
         (Printf.sprintf "mov  [rbp + %d], rax\n" (8 * (4 + minor) )) ^
         "mov rax, sob_void"

      | ScmVarSet' (Var' (v, Bound (major, minor)), expr') ->
         (* raise X_not_yet_implemented *)
         let run_parms_env=run params env expr' in
        (* i have to check that 
          from the lecture 
            run expr'
            mov rbx,  [rbp + 8 ∗ 2]
            mov rbx,  [rbx + 8 ∗ major]
            mov  [rbx + 8 ∗ minor], rax
            mov rax, sob_void     *)
         (run_parms_env) ^
         (Printf.sprintf "mov rbx,  [rbp + %d]\n" (8 * 2)) ^
         (Printf.sprintf "mov rbx,  [rbx + %d]\n" (8 * major)) ^
         (Printf.sprintf "mov  [rbx + %d], rax\n" (8 * minor)) ^
         "mov rax, sob_void"


      | ScmVarDef' (Var' (v, Free), expr') ->
         let label = search_free_var_table v free_vars in
         (run params env expr')
         ^ (Printf.sprintf "\tmov  [%s], rax\n" label)
         ^ "\tmov rax, sob_void\n"
         
      | ScmVarDef' (Var' (v, Param minor), expr') ->
         raise X_not_yet_supported (*we should not implement this*)

      | ScmVarDef' (Var' (v, Bound (major, minor)), expr') ->
         raise X_not_yet_supported (*we should not implement this*)

      | ScmBox' (Var' (v, Param minor)) -> (*raise X_not_yet_implemented*)
        let run_pram_minor=(run params env (ScmVarGet'(Var' (v, Param minor)))) in 
       (Printf.sprintf "\tmov rdi, %d\n" word_size )^ 
        "call malloc\n" ^
        "mov rbx, rax\n" ^
        run_pram_minor ^
        "mov  [rbx], rax\n" ^
        "mov rax, rbx\n"

      | ScmBox' _ -> (*raise X_not_yet_implemented*)
      (*we must throw an exception *)
      raise (X_this_should_not_happen "this v is not parm' and we try to box it .")

      | ScmBoxGet' var' ->
         (run params env (ScmVarGet' var'))
         ^ "\tmov rax,  qword[rax]\n"

      | ScmBoxSet' (var', expr') -> 
        (* raise X_not_yet_implemented *)

        (*  from the lecture :
        BoxSet'(Var'(v),E)
        run E
        push rax
        run var(V)
        pop [rax]
        mov rax, sob_void   
        *)
        let run_parms_env=run params env expr' in 
         let run_parms_env_v=run params env (ScmVarGet' var') in 
        (run_parms_env) ^
        "push rax\n" ^
        (run_parms_env_v) ^
        "pop  qword[rax]\n" ^
        "mov rax, sob_void\n"



      | ScmLambda' (params', Simple, body) ->
         let label_loop_env = make_lambda_simple_loop_env ()
         and label_loop_env_end = make_lambda_simple_loop_env_end ()
         and label_loop_params = make_lambda_simple_loop_params ()
         and label_loop_params_end = make_lambda_simple_loop_params_end ()
         and label_code = make_lambda_simple_code ()
         and label_arity_ok = make_lambda_simple_arity_ok ()
         and label_end = make_lambda_simple_end ()
         in
         "\tmov rdi, (1 + 8 + 8)\t; sob closure\n"
         ^ "\tcall malloc\n"
         ^ "\tpush rax\n"
         ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; new rib\n" params)
         ^ "\tcall malloc\n"
         ^ "\tpush rax\n"
         ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; extended env\n" (env + 1))
         ^ "\tcall malloc\n"
         ^ "\tmov rdi, ENV\n"
         ^ "\tmov rsi, 0\n"
         ^ "\tmov rdx, 1\n"
         ^ (Printf.sprintf "%s:\t; ext_env[i + 1] <-- env[i]\n"
              label_loop_env)
         ^ (Printf.sprintf "\tcmp rsi, %d\n" (env + 1))
         ^ (Printf.sprintf "\tje %s\n" label_loop_env_end)
         ^ "\tmov rcx,  [rdi + 8 * rsi]\n"
         ^ "\tmov  [rax + 8 * rdx], rcx\n"
         ^ "\tinc rsi\n"
         ^ "\tinc rdx\n"
         ^ (Printf.sprintf "\tjmp %s\n" label_loop_env)
         ^ (Printf.sprintf "%s:\n" label_loop_env_end)
         ^ "\tpop rbx\n"
         ^ "\tmov rsi, 0\n"
         ^ (Printf.sprintf "%s:\t; copy params\n" label_loop_params)
         ^ (Printf.sprintf "\tcmp rsi, %d\n" params)
         ^ (Printf.sprintf "\tje %s\n" label_loop_params_end)
         ^ "\tmov rdx,  [rbp + 8 * rsi + 8 * 4]\n"
         ^ "\tmov  [rbx + 8 * rsi], rdx\n"
         ^ "\tinc rsi\n"
         ^ (Printf.sprintf "\tjmp %s\n" label_loop_params)
         ^ (Printf.sprintf "%s:\n" label_loop_params_end)
         ^ "\tmov  qword[rax], rbx\t; ext_env[0] <-- new_rib \n"
         ^ "\tmov rbx, rax\n"
         ^ "\tpop rax\n"
         ^ "\tmov byte [rax], T_closure\n"
         ^ "\tmov SOB_CLOSURE_ENV(rax), rbx\n"
         ^ (Printf.sprintf "\tmov SOB_CLOSURE_CODE(rax), %s\n" label_code)
         ^ (Printf.sprintf "\tjmp %s\n" label_end)
         ^ (Printf.sprintf "%s:\t; lambda-simple body\n" label_code)
         ^ (Printf.sprintf "\tcmp  qword[rsp + 8 * 2], %d\n"
              (List.length params'))
         ^ (Printf.sprintf "\tje %s\n" label_arity_ok)
         ^ "\tpush  qword[rsp + 8 * 2]\n"
         ^ (Printf.sprintf "\tpush %d\n" (List.length params'))
         ^ "\tjmp L_error_incorrect_arity_simple\n"
         ^ (Printf.sprintf "%s:\n" label_arity_ok)
         ^ "\tenter 0, 0\n"
         ^ (run (List.length params') (env + 1) body)
         ^ "\tleave\n"
         ^ (Printf.sprintf "\tret 8 * (2 + %d)\n" (List.length params'))
         ^ (Printf.sprintf "%s:\t; new closure is in rax\n" label_end)
| ScmLambda' (params', Opt opt, body) ->
          let label_loop_env = make_lambda_opt_loop_env ()
          and label_loop_env_end = make_lambda_opt_loop_env_end ()
          and label_loop_params = make_lambda_opt_loop_params ()
          and label_loop_params_end = make_lambda_opt_loop_params_end ()
          and label_code = make_lambda_opt_code ()
          and label_end = make_lambda_opt_end ()
          and lambda_opt_stack_ok = make_lambda_opt_stack_ok()
          and lambda_exact_args_case = make_lambda_opt_arity_exact()
          and lambda_exact_args_case_loop = make_lambda_opt_loop()
          and lambda_exact_args_case_loop_exit = make_lambda_opt_loop_exit()
          and lambda_extra_args_case = make_lambda_opt_arity_more()
          and lambda_extra_args_case_loop = make_lambda_opt_loop()
          and lambda_extra_args_case_loop_exit = make_lambda_opt_loop_exit()
          and lambda_extra_args_case_shrink_loop = make_lambda_opt_loop()
          and lambda_extra_args_case_shrink_loop_exit = make_lambda_opt_end()
          and expected_length = (List.length params') + 1
        in
          "\tmov rdi, (1 + 8 + 8)\t; sob closure\n"
          ^ "\tcall malloc\n"
          ^ "\tpush rax\n"
          ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; new rib\n" params)
          ^ "\tcall malloc\n"
          ^ "\tpush rax\n"
          ^ (Printf.sprintf "\tmov rdi, 8 * %d\t; extended env\n" (env + 1))
          ^ "\tcall malloc\n"
          ^ "\tmov rdi, ENV\n"
          ^ "\tmov rsi, 0\n"
          ^ "\tmov rdx, 1\n"
          ^ (Printf.sprintf "%s:\t; ext_env[i + 1] <-- env[i]\n"
               label_loop_env)
          ^ (Printf.sprintf "\tcmp rsi, %d\n" (env))
          ^ (Printf.sprintf "\tje %s\n" label_loop_env_end)
          ^ "\tmov rcx,  [rdi + 8 * rsi]\n"
          ^ "\tmov  [rax + 8 * rdx], rcx\n"
          ^ "\tinc rsi\n"
          ^ "\tinc rdx\n"
          ^ (Printf.sprintf "\tjmp %s\n" label_loop_env)
          ^ (Printf.sprintf "%s:\n" label_loop_env_end)
          ^ "\tpop rbx\n"
          ^ "\tmov rsi, 0\n"
          ^ (Printf.sprintf "%s:\t; copy params\n" label_loop_params)
          ^ (Printf.sprintf "\tcmp rsi, %d\n" params)
          ^ (Printf.sprintf "\tje %s\n" label_loop_params_end)
          ^ "\tmov rdx,  [rbp + 8 * rsi + 8 * 4]\n"
          ^ "\tmov  [rbx + 8 * rsi], rdx\n"
          ^ "\tinc rsi\n"
          ^ (Printf.sprintf "\tjmp %s\n" label_loop_params)
          ^ (Printf.sprintf "%s:\n" label_loop_params_end)
          ^ "\tmov  qword[rax], rbx\t; ext_env[0] <-- new_rib \n"
          ^ "\tmov rbx, rax\n"
          ^ "\tpop rax\n"
          ^ "\tmov byte [rax], T_closure\n"
          ^ "\tmov SOB_CLOSURE_ENV(rax), rbx\n"
          ^ (Printf.sprintf "\tmov SOB_CLOSURE_CODE(rax), %s\n" label_code)
          ^ (Printf.sprintf "\tjmp %s\n" label_end)

          (* (Lambda opt code adjustment) *)
          ^ (Printf.sprintf "%s:\t; lambda-opt-body\n" label_code)

          ^"\tpush rbp\n"

          ^(Printf.sprintf "mov r10, %d\n" (expected_length))
          ^"\tmov r9,  [rsp + 8*3]\n"
          ^"\tadd r9, 1\n"
          ^"\tcmp r9, r10\n"
          ^(Printf.sprintf "\tje %s\n" lambda_exact_args_case)
          ^"\tcmp r9, r10\n"
          ^"\tjl L_error_incorrect_arity_opt\n"

          ^(Printf.sprintf "\t%s:\n" lambda_extra_args_case)
          ^"\tmov r12, r10\n"
          ^"\tmov r13, r10\n"
          ^"\tsub r13, 1\n"
          ^"\tmov r9,  [rsp + 8*3]\n"
          ^"\tsub r9, 1\n"
          ^"\tmov rdx, sob_nil\n"
          ^(Printf.sprintf "\t%s:\n" lambda_extra_args_case_loop)
          ^"\tcmp r9, r13\n"
          ^(Printf.sprintf "\tjl %s\n" lambda_extra_args_case_loop_exit)
          ^"\tmov r14,  [rsp + 8*(4+r9)]\n"
          ^"\tmov rdi, (8 + 8 + 1)\n"
          ^"\tcall malloc\n"
          ^"\tmov byte [rax], T_pair\n"
          ^"\tmov SOB_PAIR_CAR(rax), r14\n"
          ^"\tmov SOB_PAIR_CDR(rax), rdx\n"
          ^"\tmov rdx, rax\n"
          ^"\tdec r9\n"
          ^(Printf.sprintf "\tjmp %s \n" lambda_extra_args_case_loop)
          ^(Printf.sprintf "\t%s:\n" lambda_extra_args_case_loop_exit)
          ^"\tmov  [rsp + 8*(4+r13)], rdx\n"      
          ^"\tmov rdx,  [rsp + 8*3]\n"  
          ^"\tmov r13, r12\n"   
          ^"\tmov r9, rdx\n" 
          ^"\tadd r9, 3\n"  
          ^"\tadd r13, 3\n" 
          ^(Printf.sprintf "\t%s:\n" lambda_extra_args_case_shrink_loop)
          ^"\tcmp r13, 0\n"     
          ^(Printf.sprintf "\tjl %s\n" lambda_extra_args_case_shrink_loop_exit)
          ^"\tmov r14, [rsp + 8*r13]\n" 
          ^"\tmov [rsp + 8*r9], r14\n" 
          ^"\tdec r13\n" 
          ^"\tdec r9\n" 
          ^(Printf.sprintf "\tjmp %s\n" lambda_extra_args_case_shrink_loop)
          ^(Printf.sprintf "\t%s:\n" lambda_extra_args_case_shrink_loop_exit)
          ^"\tsub rdx, r12\n"
          ^"\tshl rdx, 3\n"
          ^"\tadd rsp, rdx\n" 
          ^"\tmov  [rsp + 8*3], r12\n"
          ^(Printf.sprintf "\tjmp %s\n" lambda_opt_stack_ok) 

          ^(Printf.sprintf "\t%s:\n" lambda_exact_args_case)
          ^"\tmov rdi,  [rsp + 8*3]\n"
          ^"\tadd rdi, 4\n"
          ^"\tmov rcx, 0\n"
          ^(Printf.sprintf "\t%s:\n" lambda_exact_args_case_loop)
          ^"\tcmp rdi, rcx\n"
          ^(Printf.sprintf "\tje %s\n" lambda_exact_args_case_loop_exit)
          ^"\tmov rdx,  [rsp + 8*rcx]\n"
          ^"\tmov  qword[rsp + 8*rcx - 8], rdx\n"
          ^"\tinc rcx\n"
          ^(Printf.sprintf "\tjmp %s\n" lambda_exact_args_case_loop)
          ^(Printf.sprintf "\t%s:\n" lambda_exact_args_case_loop_exit)
          ^"\tmov  qword[rsp + 8*rcx - 8], sob_nil\n"
          ^"\tlea rsp,  [rsp - 8]\n"
          ^"\tmov  [rsp + 8*3], r10\n"

          ^(Printf.sprintf "\t%s:\n" lambda_opt_stack_ok)
          ^"\tpop rbp\n"

          ^ "\tenter 0, 0\n"
          ^ (run (expected_length) (env + 1) body)
          ^ "\tleave\n"
          ^ (Printf.sprintf "\tret 8 * (2 + %d)\n" (expected_length))
          ^ (Printf.sprintf "%s:\t; new closure is in rax\n" label_end)   
| ScmApplic' (proc, args, Non_Tail_Call) -> 

          (String.concat "" (List.map (fun arg -> (run params env arg)^"\tpush rax\n") (List.rev args)))^
          (Printf.sprintf "\tpush %d\n" (List.length args))^
          (run params env proc)^
          "\tassert_closure(rax)\n"^
          "\tpush SOB_CLOSURE_ENV(rax)\n"^
          "\tcall SOB_CLOSURE_CODE(rax)\n"

          | ScmApplic' (proc, args, Tail_Call) ->

            let applic_tc_loop = make_tc_applic_recycle_frame_loop()
            and applic_tc_loop_end = make_tc_applic_recycle_frame_done() in
            (String.concat "" (List.map (fun arg -> (run params env arg)^"\tpush rax\n") (List.rev args)))^
            (Printf.sprintf "\tpush %d\n" (List.length args))^
            (run params env proc)^
            "\tassert_closure(rax)\n"^
            "\tpush SOB_CLOSURE_ENV(rax)\n"^
            "\tpush RET_ADDR\n"^
            "\tpush OLD_RDP\n"^

            (Printf.sprintf "\tmov rbx, %d\n" (List.length args))^
            "\tadd rbx, 3\n"^
            "\tmov rcx, COUNT\n"^
            "\tadd rcx, 3\n"^
            (Printf.sprintf "\t%s:\n" applic_tc_loop)^
            "\tcmp rbx, 0\n"^
            (Printf.sprintf "\tjl %s\n" applic_tc_loop_end)^
            "\tmov rdx,  [rsp + 8*rbx]\n"^
            "\tmov  [rbp + 8*rcx], rdx\n"^
            "\tdec rbx\n"^
            "\tdec rcx\n"^
            (Printf.sprintf "\tjmp %s\n" applic_tc_loop)^
            (Printf.sprintf "\t%s:\n" applic_tc_loop_end)^
          
            "\tlea rsp,  [rbp + 8*rcx + 8]\n"^

            "\tpop rbp\n"^
            "\tjmp SOB_CLOSURE_CODE(rax)\n"
    and runs params env exprs' =
      List.map
        (fun expr' ->
          let code = run params env expr' in
          let code =
            code
            ^ "\n\tmov rdi, rax"
            ^ "\n\tcall print_sexpr_if_not_void\n" in
          code)
        exprs' in
    let codes = runs 0 0 exprs' in
    let code = String.concat "\n" codes in
    let code =
      (file_to_string "prologue-1.asm")
      ^ (asm_of_constants_table consts)
      ^ "\nsection .bss\n"
      ^ (asm_of_free_vars_table free_vars)
      ^ (file_to_string "prologue-2.asm")
      ^ (asm_of_global_bindings global_bindings_table free_vars)
      ^ "\n"
      ^ code
      ^ (file_to_string "epilogue.asm") in
    code;;

  let compile_scheme_string file_out user =
    let init = file_to_string "init.scm" in
    let source_code = init ^ user in
    let sexprs = (PC.star Reader.nt_sexpr source_code 0).found in
    let exprs = List.map Tag_Parser.tag_parse sexprs in
    let exprs' = List.map Semantic_Analysis.semantics exprs in
    let asm_code = code_gen exprs' in
    (string_to_file file_out asm_code;
     Printf.printf "!!! Compilation finished. Time to assemble!\n");;  

  let compile_scheme_file file_in file_out =
    compile_scheme_string file_out (file_to_string file_in);;

end;; (* end of Code_Generation struct *)

(* end-of-input *)

