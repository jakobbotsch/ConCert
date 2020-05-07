From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Certified.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import StringExtra.

From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import PArith.
From Coq Require Import String.

From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.
From MetaCoq.Template Require Import All.
From MetaCoq.Erasure Require Import Debox Loader SafeTemplateErasure EAst EAstUtils ETyping.

Module P := MetaCoq.PCUIC.PCUICAst.
Module PT := MetaCoq.PCUIC.PCUICTyping.
Module T2P := MetaCoq.PCUIC.TemplateToPCUIC.
Module E := MetaCoq.Erasure.EAst.
Module T := MetaCoq.Template.Ast.
Module TUtil := MetaCoq.Template.AstUtils.
Module EF := MetaCoq.Erasure.SafeErasureFunction.
Module Ex := Common.

Import PrettyPrinterMonad.
Import ListNotations.
Import MonadNotation.

Local Open Scope string.
Local Open Scope list.

Local Definition indent_size := 2.

Section FixExEnv.
Context (Σ : Ex.global_env).

Definition get_fun_name (name : kername) : string :=
  uncapitalize (replace_char "." "_" name).

Definition get_ty_name (name : kername) : string :=
  capitalize (replace_char "." "_" name).

Definition get_ctor_name (name : ident) : string :=
  capitalize name.

Definition get_ty_arg_name (name : ident) : ident :=
  uncapitalize name.

Definition lookup_mind (name : kername) : option P.mutual_inductive_body :=
  match Ex.lookup_env Σ name with
  | Some (Ex.InductiveDecl mib) => Some mib
  | _ => None
  end.

Definition lookup_ind_decl (ind : inductive) : PrettyPrinter P.one_inductive_body :=
  match lookup_mind (inductive_mind ind) with
  | Some {| P.ind_bodies := l |} =>
    match nth_error l (inductive_ind ind) with
    | Some body => ret body
    | None => printer_fail ("could not find inductive " ++
                            string_of_nat (inductive_ind ind) ++
                            " in inductive " ++ inductive_mind ind)
    end
  | _ => printer_fail ("could not find " ++ inductive_mind ind ++ " in environment")
  end.

Definition print_ind_ctor (ind : inductive) (i : nat) : PrettyPrinter unit :=
  oib <- lookup_ind_decl ind;;
  match nth_error (P.ind_ctors oib) i with
  | Some (name, _, _) =>
    append (get_ctor_name name)
    (*append (replace_char "." "_" (inductive_mind ind) ++ "_" ++ name)*)
  | None =>
    printer_fail (inductive_mind ind ++ " does not have a ctor " ++ string_of_nat i)
  end.

Definition print_parenthesized
           (parenthesize : bool)
           (print : PrettyPrinter unit) : PrettyPrinter unit :=
  if parenthesize then
    append "(";; print;; append ")"
  else
    print.

Definition parenthesize_app_head (t : term) : bool :=
  match t with
  | tLambda _ _
  | tLetIn _ _ _
  | tCase _ _ _
  | tFix _ _ => true
  | _ => false
  end.

Definition parenthesize_app_arg (t : term) : bool :=
  match t with
  | tLambda _ _
  | tLetIn _ _ _
  | tApp _ _
  | tCase _ _ _
  | tProj _ _
  | tFix _ _ => true
  | _ => false
  end.

Definition parenthesize_case_discriminee (t : term) : bool :=
  match t with
  | tLetIn _ _ _
  | tCase _ _ _ => true
  | _ => false
  end.

Definition parenthesize_case_branch (t : term) : bool :=
  false.

Definition fresh (name : ident) (used : list ident) : ident :=
  if existsb (String.eqb name) used then
    (fix f n i :=
       match n with
       | 0 => "unreachable"
       | S n =>
         let numbered_name := (name ++ string_of_nat i)%string in
         if existsb (String.eqb numbered_name) used then
           f n (S i)
         else
           numbered_name
       end) (S (List.length used)) 2
  else
    name.

Definition fresh_ident (name : name) (Γ : list ident) : PrettyPrinter ident :=
  used_names <- get_used_names;;
  match name with
  | nAnon => ret (fresh "_x" (Γ ++ used_names))
  | nNamed name => ret (fresh (remove_char "'" name) (Γ ++ used_names))
  end.

Definition fresh_ty_arg_name (name : name) (Γ : list ident) : PrettyPrinter ident :=
  used_names <- get_used_names;;
  match name with
  | nAnon => ret (fresh "a" (Γ ++ used_names))
  | nNamed name => ret (fresh (get_ty_arg_name name) (Γ ++ used_names))
  end.

Import P.
Definition parenthesize_prod_domain (t : term) : bool :=
  match t with
  | tProd _ _ _ => true
  | _ => false
  end.

Definition parenthesize_ty_app_arg (t : term) : bool :=
  match t with
  | tApp _ _ => true
  | _ => false
  end.

Fixpoint print_type (Γ : list (option ident)) (t : term) : PrettyPrinter unit :=
  match t with
  | tRel n =>
    match nth_error Γ n with
    | Some (Some name) => append name
    | Some None =>
      printer_fail ("cannot print type with dependencies:" ++ nl ++ PCUICAstUtils.string_of_term t)
    | None =>
      printer_fail ("unbound tRel " ++ string_of_nat n)
    end
  | tInd ind _ => append (get_ty_name (inductive_mind ind))
  | tProd name (tSort _) cod =>
    (* Midlang is implicitly generalized over type args *)
    let or_empty o :=
        match o with
        | Some n => n
        | None => ""
        end in
    name <- fresh_ty_arg_name name (map or_empty Γ);;
    print_type (Some name :: Γ) cod
  | tProd _ dom cod =>
    print_parenthesized (parenthesize_prod_domain dom) (print_type Γ dom);;
    append " -> ";;
    print_type (None :: Γ) cod
  | tApp head arg =>
    print_type Γ head;;
    append " ";;
    print_parenthesized (parenthesize_ty_app_arg arg) (print_type Γ arg)
  | _ => printer_fail ("cannot print following as type" ++ nl ++ PCUICAstUtils.string_of_term t)
  end.

Import E.
(* Print something of the form
   foo =
     a b c
inlining lambdas and fix points. For example, for
   foo = \x \y \z -> z
instead print
   foo x y z = z
*)
Definition print_define_term
         (Γ : list ident)
         (name : ident)
         (t : term)
         (print_term : list ident -> term -> PrettyPrinter unit) : PrettyPrinter unit :=
  name_col <- get_current_line_length;;
  append name;;

  let fix print_decompose Γ t :=
      match t with
      | tLambda arg_name t =>
        arg_name <- fresh_ident arg_name Γ;;
        append (" " ++ arg_name);;
        print_decompose (arg_name :: Γ) t
      | _ =>
        append " =";;
        push_indent (name_col + indent_size);;
        append_nl_and_indent;;
        print_term Γ t;;
        pop_indent
      end in

  match t with
  | tFix [d] 0 => print_decompose (name :: Γ) (dbody d)
  | _ => print_decompose Γ t
  end.

Fixpoint print_term (Γ : list ident) (t : term) : PrettyPrinter unit :=
  match t with
  | tBox _ => printer_fail "tBox"
  | tRel n =>
    match nth_error Γ n with
    | Some name => append name
    | None => printer_fail ("unbound tRel " ++ string_of_nat n)
    end
  | tVar ident => printer_fail ("tVar " ++ ident)
  | tEvar _ _ => printer_fail "unexpected evar"
  | tLambda name t =>
    append "\";;

    name <- fresh_ident name Γ;;
    append name;;
    append " -> ";;
    print_term (name :: Γ) t

  | tLetIn name value body =>

    let_col <- get_current_line_length;;
    push_indent let_col;;

    append "let";;

    let print_and_add_one Γ name value :=
        append_nl_and_indent;;
        name <- fresh_ident name Γ;;
        (* We will define this name to make sure we don't reuse it
           until the let is all over. Midlang does not allow shadowing. *)
        push_use name;;
        print_define_term Γ name value print_term;;
        ret (name :: Γ) in

    push_indent (let_col + indent_size);;

    Γ <- print_and_add_one Γ name value;;

    (* Print in Midlang/Elm style, which collapses multiple lets into one *)
    (* Turned off because of Elm's insane shadowing rules *)
    (*
    num_collapsed <-
    (fix print_lets Γ (t : term) :=
       match t with
       | tLetIn name value t =>
         Γ <- print_and_add_one Γ name value;;
         n <- print_lets Γ t;;
         ret (S n)
       | _ =>
         pop_indent;; (* indent in let block *)

         append_nl_and_indent;; (* indent to 'let' keyword *)
         append "in";;

         append_nl_and_indent;; (* body is indented to 'let'/'in' keyword as well *)
         print_term Γ t;;
         pop_indent;;
         ret 0
       end) Γ body;;

    (* pop all the names we defined, we can reuse those names now. *)
    monad_fold_left (fun _ _ => pop_use) (repeat tt (S num_collapsed)) tt
    *)

    pop_indent;;
    append_nl_and_indent;;

    append "in";;
    append_nl_and_indent;;
    print_term Γ body;;
    pop_indent;;

    pop_use

  | tApp head arg =>
    print_parenthesized (parenthesize_app_head head) (print_term Γ head);;
    append " ";;
    print_parenthesized (parenthesize_app_arg arg) (print_term Γ arg)

  | tConst name => append (get_fun_name name)
  | tConstruct ind i => print_ind_ctor ind i

  | tCase (ind, _) discriminee branches =>
    case_col <- get_current_line_length;;
    append "case ";;
    print_parenthesized (parenthesize_case_discriminee discriminee)
                        (print_term Γ discriminee);;
    append " of";;

    push_indent (case_col + indent_size);;

    oib <- lookup_ind_decl ind;;

    (* Take care that this is structurally recursive... *)
    (fix print_branches (branches : list (nat * term)) (ctor_names : list ident) :=
       match branches, ctor_names with
       | [], [] => ret tt
       | (arity, t) :: branches, ctor_name :: ctor_names =>
         append_nl_and_indent;;

         ctor_indent <- get_indent;;
         push_indent (ctor_indent + indent_size);;

         append (get_ctor_name ctor_name);;

         (fix print_branch (n : nat) (Γ : list ident) (t : term) {struct t} :=
            match n with
            | 0 =>
              append " ->";;
              append_nl_and_indent;;
              print_parenthesized (parenthesize_case_branch t) (print_term Γ t)

            | S n =>
              match t with
              | tLambda name t =>
                name <- fresh_ident name Γ;;
                append (" " ++ name);;
                print_branch n (name :: Γ) t

              | _ => printer_fail "could not decompose branch"
              end
            end) arity Γ t;;

         pop_indent;;

         print_branches branches ctor_names
       | _, _ => printer_fail "wrong number of case branches compared to inductive"
       end) branches (map (fun '(name, _, _) => name) (P.ind_ctors oib));;

    pop_indent

  | tProj _ _ => printer_fail "tProj"

  | tFix mfix nfix =>
    let_col <- get_current_line_length;;
    push_indent let_col;;

    (* Add names of fixes to context *)
    Γ <- monad_fold_left
           (fun Γ d => name <- fresh_ident (dname d) Γ;;
                       ret (name :: Γ)) mfix Γ;;
    let names := rev (firstn (List.length mfix) Γ) in

    append "let";;

    push_indent (let_col + indent_size);;

    (fix print_fixes (ds : list (def term)) (names : list ident) :=
       match ds, names with
       | [], _ => ret tt
       | d :: ds, name :: names =>
         append_nl_and_indent;;
         print_define_term Γ name (dbody d) print_term;;
         print_fixes ds names
       | _, _ =>
         printer_fail "unreachable"
       end) mfix names;;

    pop_indent;;

    append_nl_and_indent;;
    append "in";;
    append_nl_and_indent;;
    match nth_error names nfix with
    | Some n => append n
    | None => printer_fail "invalid fix index"
    end;;

    pop_indent

  | tCoFix _ _ => printer_fail "Cannot handle cofix"
  end.

Definition print_constant_body
           (name : kername)
           (cst : Ex.constant_body) : PrettyPrinter string :=
  name_col <- get_current_line_length;;

  push_indent name_col;;

  let (type, body) := cst in

  let ml_name := get_fun_name name in
  (*
  append ml_name;;
  append " : ";;
  print_type [] type;;*)

  match body with
  | None => ret tt
  | Some body =>
    let name := get_fun_name name in
    push_use name;;
    print_define_term [] name body print_term
  end;;

  pop_indent;;

  ret ml_name.

Quote Recursively Definition foo := (None : option nat)%nat.

Definition decompose_ind_ctor
         (nparams : nat)
         (arity : nat)
         (t : P.term) : PrettyPrinter (list P.term) :=
  (* First get rid of parameters. The constructor will always start with those *)
  t <- (fix f n t :=
           match n, t with
           | 0, _ => ret t
           | S n, tProd _ (tSort _) t => f n t
           | _, _ => printer_fail ("unexpected type of ctor: " ++ PCUICAstUtils.string_of_term t)
           end) nparams t;;

  (fix f n t :=
     match n with
     | 0 => ret []
     | S n =>
       match t with
       | P.tProd _ dom cod =>
         tl <- f n cod;;
         ret (dom :: tl)
       | _ =>
         printer_fail ("unexpected type of ctor: " ++ PCUICAstUtils.string_of_term t)
       end
     end) arity t.

Import P.
Definition parenthesize_ind_ctor_ty (ty : term) : bool :=
  match ty with
  | tInd _ _
  | tVar _
  | tRel _ => false
  | _ => true
  end.

Definition print_ind_ctor_definition
           (Γ : list (option ident))
           (name : ident)
           (ty : P.term)
           (nparams : nat)
           (arity : nat) : PrettyPrinter unit :=
  append (get_ctor_name name);;
  tys <- decompose_ind_ctor nparams arity ty;;

  (fix f (Γ : list (option ident)) (tys : list P.term) :=
     match tys with
     | [] => ret tt
     | ty :: tys =>
       append " ";;
       print_parenthesized (parenthesize_ind_ctor_ty ty) (print_type Γ ty);;
       f (None :: Γ) tys
     end) Γ tys.

Local Open Scope string.
Definition print_mutual_inductive_body
           (name : kername)
           (mib : P.mutual_inductive_body) : PrettyPrinter (list (kername * string)) :=
  col <- get_current_line_length;;
  push_indent col;;

  let qualifier := kername_qualifier name in

  (* make context that has mutual inductive bodies *)
  let Γ := rev_map (fun oib => get_ty_name (qualifier ++ "." ++ ind_name oib)) (ind_bodies mib) in
  (* add parameters *)
  Γ <- monad_fold_left
         (fun Γ d =>
            match decl_body d with
            | None => ret tt
            | Some _ => printer_fail "cannot handle inductive parameter with body"
            end;;
            match decl_type d with
            | tSort _ => ret tt
            | t => printer_fail "can only handle parameters of type sort"
            end;;
            name <- fresh_ty_arg_name (decl_name d) Γ;;
            ret (name :: Γ)) (rev (ind_params mib)) Γ;;

  let ty_arg_names := rev (firstn (List.length (ind_params mib)) Γ) in

  names <-
  (fix print_ind_bodies
       (l : list P.one_inductive_body)
       (first : bool)
       (names : list (kername * string)) :=
     match l with
     | [] => ret names
     | oib :: l =>

       (if first then ret tt else append_nl_and_indent);;

       append "type ";;
       let ind_name := qualifier ++ "." ++ P.ind_name oib in
       let ind_ml_name := get_ty_name ind_name in
       append ind_ml_name;;

       (* Print type args *)
       monad_fold_left (fun _ name => append (" " ++ name)) ty_arg_names tt;;

       push_indent (col + indent_size);;

       (fix print_ind_ctors (ctors : list (ident * P.term * nat)) prefix :=
          match ctors with
          | [] => ret tt
          | (name, ty, arity) :: ctors =>
            append_nl_and_indent;;
            append (prefix ++ " ");;
            print_ind_ctor_definition (map Some Γ) name ty (ind_npars mib) arity;;

            print_ind_ctors ctors "|"
          end) (ind_ctors oib) "=";;

       pop_indent;;

       print_ind_bodies l false ((ind_name, ind_ml_name) :: names)
     end) (ind_bodies mib) true [];;

  pop_indent;;

  ret names.

Definition print_global_decl
           (name : kername)
           (decl : Ex.global_decl) : PrettyPrinter (list (kername * string)) :=
  match decl with
  | Ex.ConstantDecl cst => ml_name <- print_constant_body name cst;;
                           ret [(name, ml_name)]
  | Ex.InductiveDecl mib => print_mutual_inductive_body name mib
  end.

Definition print_env : PrettyPrinter (list (kername * string)) :=
  sig_col <- get_current_line_length;;
  push_indent sig_col;;

  names <- (fix f (l : Ex.global_env) (first : bool) (names : list (kername * string)) :=
     match l with
     | [] => ret names
     | (name, decl) :: l =>

       (if first then ret tt else (append_nl;; append_nl_and_indent));;
       new_names <- print_global_decl name decl;;

       f l false (new_names ++ names)%list
     end) Σ true [];;

  pop_indent;;

  ret names.
End FixExEnv.

Axiom assump : string -> forall {A}, A.

Lemma proj_wf
      {Σ : P.global_env_ext}
      (wfΣ : ∥PT.wf_ext Σ∥) : ∥PT.wf Σ.1∥.
Proof. firstorder. Qed.

Definition erase_and_debox_single
           (Σ : P.global_env_ext)
           (wfΣ : ∥PT.wf_ext Σ∥)
           (decl : P.global_decl) : PrettyPrinter Ex.global_decl :=
  match decl with
  | P.ConstantDecl cst =>
    let (type, body, _) := cst in
    match body with
    | None => ret (Ex.ConstantDecl {| Ex.cst_type := type; Ex.cst_body := None |})
    | Some body =>
      ebody <- wrap_typing_result
                 Σ.1
                 (EF.erase Σ wfΣ [] body (assump "assuming well-typedness"));;
      result <- wrap_EnvCheck (check_applied Σ.1 ebody (proj_wf wfΣ));;
      if result then
        let ebody := debox_top_level (debox_all ebody) in
        ret (Ex.ConstantDecl {| Ex.cst_type := type; Ex.cst_body := Some ebody |})
      else
        printer_fail "Not all constructors or constants are appropriately applied"
    end
  | P.InductiveDecl mib =>
    ret (Ex.InductiveDecl mib)
  end.

Definition ignored_concert_types :=
  ["ConCert.Execution.Blockchain.ChainBase";
   "ConCert.Execution.Blockchain.Chain";
   "ConCert.Execution.Blockchain.ContractCallContext"].

Lemma wf_empty_ext (Σ : P.global_env) :
  ∥PT.wf Σ∥ -> ∥PT.wf_ext (P.empty_ext Σ)∥.
Proof.
  intros [wfΣ].
  constructor.
  split; [assumption|].
  todo "on_udecl on empty_ext".
Qed.

Definition preprocess_for_extraction
           (name : kername)
           (decl : Ex.global_decl) : PrettyPrinter Ex.global_decl :=
  match decl with
  | Ex.ConstantDecl body =>
    let (ty, body) := body in
    match body with
    | None => ret (Ex.ConstantDecl {| Ex.cst_type := ty; Ex.cst_body := None |})
    | Some body =>
      if uses_account_balance body then
        printer_fail ("'" ++ name ++ "' uses account_balance")
      else
        '(type, body) <- wrap_result (ungeneralize_ChainBase ty body) id;;
        ret (Ex.ConstantDecl {| Ex.cst_type := type; Ex.cst_body := Some body |})
    end
  | _ => ret decl
  end.

(* Extract the specified environment to Midlang, creating definitions for all symbols. *)
Definition extract_env (Σ : T.global_env) : PrettyPrinter unit :=
  let remove_universe_constraints (decl : T.global_decl) :=
      match decl with
      | T.ConstantDecl body =>
        let (type, body, _) := body in
        T.ConstantDecl {| T.cst_type := type;
                          T.cst_body := body;
                          T.cst_universes := Monomorphic_ctx ContextSet.empty |}
      | T.InductiveDecl mib =>
        let (finite, npars, params, bodies, _, variance) := mib in
        T.InductiveDecl {| T.ind_finite := finite;
                           T.ind_npars := npars;
                           T.ind_params := params;
                           T.ind_bodies := bodies;
                           T.ind_universes := Monomorphic_ctx ContextSet.empty;
                           T.ind_variance := variance |}
      end in
  let Σ := map (fun '(name, d) => (name, remove_universe_constraints d)) Σ in
  let Σ := fix_global_env_universes Σ in
  let Σ := (T2P.trans_global (T.empty_ext Σ)).1 in
  G <- wrap_EnvCheck (check_wf_env_only_univs Σ);;
  let wfΣ := G.π2.p2 in
  let Σext := P.empty_ext Σ in
  let wfΣext : ∥PT.wf_ext Σext∥ := wf_empty_ext Σ wfΣ in
  Σex <- monad_map (fun '(name, decl) =>
                      decl <- erase_and_debox_single Σext wfΣext decl;;
                      ret (name, decl)) Σ;;
  let seeds := ["ConCert.Extraction.MidlangExtract.init";
                "ConCert.Extraction.MidlangExtract.receive"] in
  to_extract <- wrap_result (decl_deps_recursive Σex seeds ignored_concert_types)
                            id;;
  to_extract <- monad_map (fun '(name, decl) => decl <- preprocess_for_extraction name decl;;
                                                ret (name, decl)) to_extract;;
  (*monad_fold_left (fun _ '(name, _) => append name;; append_nl) to_extract tt;;*)
  print_env to_extract;;
  ret tt.

(*
Local Open Scope nat.

Inductive Msg :=
| increment (nums : list nat)
| decrement.

Definition recv (state : nat) (maybe_msg : option Msg) :=
  match maybe_msg with
  | Some (increment nums) => Some (state + fold_left Nat.add (nums ++ nums) 0 - fold_right Nat.mul 0 nums)
  | Some decrement => Some (state - 1)
  | _ => None
  end.

Definition app (f : nat -> nat) (n : nat) : nat :=
  f n.

Definition test : nat :=
  let x := 5 in
  let foo n := S n in
  let even :=
      fix even n :
        match n with
        | 0 => true
        | S n => odd n
        end
     with odd n :=
        match n with
        | 0 => false
        | S n => even n
        end
      for even in
  let fix even n :=
      match n with
      | 0 => true
      | 1 => false
      | S (S n) => even n
      end in
  let y := 7 in
  x + app (fun x => S x) (foo 3) + y + foo (foo x) + if even x then 2 else 0.

Definition test' : bool :=
  let x := let y := true in y in
  let y := x in y.

Definition list_debruijn := fold_right (fun b a => b) 0 [].
  (*(fun (x : list nat) =>
     match x with
     | nil => nil
     | y :: ys => x
     end).*)

Definition fun_fix {A} (f : nat -> A -> A) (a : A) :=
  fix g (l : list nat) : A :=
    match l with
    | [] => a
    | n :: l => f n (g l)
    end.

(*Quote Recursively Definition test_program := test.*)
(*Quote Recursively Definition test_program := (init; recv).*)
(*Quote Recursively Definition test_program := list_debruijn.*)
(*Quote Recursively Definition test_program := fun_fix.*)

Local Open Scope string.
Definition test3 :=
  match finish_print (append_nl;; extract_env test_program.1) with
  | inl err => "Printer error: " ++ err
  | inr (_, output) => output
  end.

Definition foo' := fun x => x = 5.

Quote Recursively Definition aaa := (fun x => x = 5).

Compute erase_template_program aaa.

Compute erase_check_debox_all_print [] "foo" [] test_program.

Definition test2 : string :=
  match erase_check_debox_all [] test_program with
  | CorrectDecl (Σ, (args, term)) =>
    match finish_print (append_nl;; print_term Σ ["f"] term) with
    | inl err => "Printer error: " ++ err
    | inr (_, output) => output
    end
  | EnvError Σ (AlreadyDeclared id) => "Already declared: " ++ id
  | EnvError Σ (IllFormedDecl id e) =>
    "Type error: " ++ PCUICSafeChecker.string_of_type_error Σ e ++ ", while checking " ++ id
  end.

Compute test2.
*)

From Coq Require Import ZArith.

Section Counter.
Context `{ChainBase}.
Inductive Msg :=
| increment
| decrement.

Global Instance Serializable_Msg : Serializable Msg :=
  Derive Serializable Msg_rect<increment, decrement>.

Local Open Scope Z.
Definition init
           (chain : Chain)
           (ctx : ContractCallContext)
           (setup : unit) : option Z :=
  Some 0%Z.

Definition receive
           (chain : Chain)
           (ctx : ContractCallContext)
           (state : Z)
           (maybe_msg : option Msg)
  : option (Z * list ActionBody) :=
  match maybe_msg with
  | Some increment => Some (state + 1, [])
  | Some decrement => Some (state - 1, [])
  | _ => None
  end.

Program Definition contract : Contract unit Msg Z :=
  {| Blockchain.init := init; Blockchain.receive := receive; |}.

End Counter.

Local Open Scope nat.

Import T.
Definition extract_def_name {A : Type} (a : A) : TemplateMonad qualid :=
  a <- tmEval cbn a;;
  quoted <- tmQuote a;;
  let (head, args) := TUtil.decompose_app quoted in
  match head with
  | tConst name _ => ret name
  | _ => tmFail ("Expected constant at head, got " ++ TUtil.string_of_term head)
  end.

Quote Recursively Definition test_program := (init, receive).

Definition extracted :=
  match finish_print (append_nl;; extract_env test_program.1) with
  | inl err => ("Printer error: " ++ err)%string
  | inr (_, output) => output
  end.

Compute extracted.

Definition toMidlang
           {Setup Msg State}
           `{Serializable Setup}
           `{Serializable Msg}
           `{Serializable State}
           (contract : forall (cb : ChainBase), Contract Setup Msg State) : TemplateMonad unit :=
  init_name <- extract_def_name (Blockchain.init (contract extraction_chain_base));;
  receive_name <- extract_def_name (Blockchain.receive (contract extraction_chain_base));;
  x <- erasable_program receive_name;;
  tmMsg (string_of_term x.2).

Run TemplateProgram (toMidlang (fun cb => @contract cb)).

Definition test : TemplateProgram unit :=
  tmEval

Definition foo (m : FMap nat nat) : option nat :=
  FMap.find 3 m.
