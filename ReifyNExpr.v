Require Import Coq.Strings.String.
Require Import Template.All.
Require Import Switch.Switch.
Require Import Coq.Lists.List.

Import MonadNotation.
Import ListNotations.

Require Import NExpr.
Require Import EvalNExpr.

Definition NExpr_term_equiv (σ: evalContext) (d: NExpr) (s: nat) : Prop :=
  forall (Γ: evalContext), evalNexp (σ ++ Γ) d = Some s.

Run TemplateProgram (mkSwitch string
                              eq_string
                              [("Coq.Init.Nat.add", "n_Add") ;
                                 ("Coq.Init.Nat.sub", "n_Sub") ;
                                 ("Coq.Init.Nat.mul", "n_Mul")]
                              "NOp_Names" "parse_NOp_Name").

Definition inat :=  {| inductive_mind := "Coq.Init.Datatypes.nat";
                       inductive_ind := 0 |}.
Definition nt := tInd inat [].
Definition ilist := {| inductive_mind := "Coq.Init.Datatypes.list";
                       inductive_ind := 0 |}.

Definition varlist:Type := list string.

Fixpoint compileNExpr (params:varlist) (a_n:term): TemplateMonad (varlist*NExpr) :=
  match a_n with
  | tConstruct inat 0 [] => tmReturn (params, NConst 0)
  | tApp (tConstruct inat 1 []) [e] =>
    d_e <- compileNExpr params e ;;
        let '(_, d_e') := d_e in
        tmReturn (params, (match d_e' with
                           | NConst v => NConst (S v)
                           | o => NPlus o (NConst 1)
                           end))
  | tApp (tConst bfun []) [ a_a ; a_b] =>
    d_a <- compileNExpr params a_a ;;
        d_b <- compileNExpr params a_b ;;
        let '(_, d_a') := d_a in
        let '(_, d_b') := d_b in
        match parse_NOp_Name bfun with
        | Some n_Add => tmReturn (params, NPlus  d_a' d_b')
        | Some n_Sub => tmReturn (params, NMinus d_a' d_b')
        | Some n_Mul => tmReturn (params, NMult  d_a' d_b')
        | None => tmFail ("Unknown binary function" ++ bfun)
        end
  | tLambda (nNamed n) nt b_n =>  compileNExpr (n::params) b_n
  | tRel n => tmReturn (params, NVar n)
  | _ => tmFail ("Unsupported NExpr" ++ (string_of_term a_n))
  end.

Fixpoint build_param_list (l:varlist) : TemplateMonad term :=
  match l with
  | [] => tmReturn (tApp (tConstruct ilist 0 []) [nt])
  | x::xs => ts <- build_param_list xs ;;
               tmReturn (tApp (tConstruct ilist 1 []) [nt; tRel (length xs); ts])
  end.

Definition build_forall (p:varlist) conc :=
  fold_right (fun n ps => tProd (nNamed n) nt ps) conc p.

Polymorphic Definition reifyNExp@{t u} {A:Type@{t}}
            (res_name: string)
            (lemma_name: string)
            (nexpr:A):
  TemplateMonad@{t u} unit :=
  e <- tmEval cbv nexpr ;;
    ast <- tmQuote e ;;
    cast <- compileNExpr [] ast ;;
    let '(params, c) := cast in
    c' <- tmEval cbv c ;; (* extra cbv to fold nat constructors *)
       (* definition with resuting NExpr *)
       def <- tmDefinition res_name c' ;;
       (* lemma *)
       a_params <- build_param_list params ;;
       let param_idx := map tRel (seq 0 (length params)) in
       let a_exp := tApp ast param_idx in
       a_c <- tmQuote c' ;;
           let lemma_concl := tApp (tConst "NExpr_term_equiv" []) [a_params; a_c; a_exp] in
           let lemma_ast := build_forall params lemma_concl in
           (tmBind (tmUnquoteTyped Prop lemma_ast)
                   (fun lemma_body => tmLemma lemma_name lemma_body
                                           ;;
                                           tmReturn tt)).

(* --- Reification example --- *)

Opaque Nat.add Nat.sub Nat.mul.

Example Ex1 (a b c: nat) := fun x => 2 + a*x*x + b*x + c.

Run TemplateProgram (reifyNExp "Ex1_def" "Ex1_lemma" Ex1).
Next Obligation.
  intros Γ.
  reflexivity.
Qed.

Print Ex1_def.
Check Ex1_lemma.
