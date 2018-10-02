Require Import Coq.Strings.String.
Require Import Template.All.
Require Import Switch.Switch.
Require Import Coq.Lists.List.

Import MonadNotation.
Import ListNotations.

Require Import NExpr.
Require Import EvalNExpr.

Definition NExpr_term_equiv (σ: evalContext) (d: NExpr) (s: nat)  : Prop :=
  forall (Γ: evalContext), evalNexp (σ ++ Γ) d = Some s.

Example Ex1 (a b c: nat) := fun x => 2 + a*x*x + b*x + c.

Definition string_beq a b := if string_dec a b then true else false.

Run TemplateProgram
    (mkSwitch string
              string_beq
              [("Coq.Init.Nat.add", "n_Add") ;
                 ("Coq.Init.Nat.sub", "n_Sub") ;
                 ("Coq.Init.Nat.mul", "n_Mul")]
              "NOp_Names" "parse_NOp_Name"
    ).

Section Reify.
  Local Definition inat :=  {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |}.
  Local Definition nt := tInd inat [].

  Local Opaque Nat.add Nat.sub Nat.mul.

  Definition varlist:Type := list string.

  Fixpoint compileNExpr (params:varlist) (a_n:term): TemplateMonad (varlist*NExpr) :=
    match a_n with
    | (tConstruct inat 0 []) => tmReturn (params, NConst 0)
    | (tApp (tConstruct inat 1 []) [e]) =>
      d_e <- compileNExpr params e ;;
          let '(_, d_e') := d_e in
          tmReturn (params, (match d_e' with
                             | NConst v => NConst (v+1)
                             | o => NPlus o (NConst 1)
                             end))
    | (tApp (tConst bfun []) [ a_a ; a_b]) =>
      d_a <- compileNExpr params a_a ;;
          d_b <- compileNExpr params a_b ;;
          let '(_, d_a') := d_a in
          let '(_, d_b') := d_b in
          match parse_NOp_Name bfun with
          | Some n_Add => tmReturn (params, NPlus d_a' d_b')
          | Some n_Sub => tmReturn (params, NMinus d_a' d_b')
          | Some n_Mul => tmReturn (params, NMult d_a' d_b')
          | None => tmFail ("Unknown binary function" ++ bfun)
          end
    | (tLambda (nNamed n) nt b_n) =>  compileNExpr (n::params) b_n
    | tRel n => tmReturn (params, NVar n)
    | _ => tmFail ("Unsupported NExpr" ++ (string_of_term a_n))
    end.

  Fixpoint build_param_list (l:varlist) : TemplateMonad term :=
    match l with
    | [] => tmReturn (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 0 []) [nt])
    | x::xs =>
      let i := length xs in
      ts <- build_param_list xs ;;
         tmReturn (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 1 []) [nt; tRel i; ts])
    end.

  Fixpoint iota (from:nat) (len: nat) : list nat :=
    match len with
    | O => []
    | S len' => List.cons from (iota (S from) len')
    end.

  Fixpoint build_forall (p:varlist) conc :=
    match p with
    | [] => conc
    | n::ps => tProd (nNamed n) nt (build_forall ps conc)
    end.

  Definition build_forall' (p:varlist) conc :=
    List.fold_right (fun n ps => tProd (nNamed n) nt ps) conc p.

  Polymorphic Definition reifyNExp@{t u} {A:Type@{t}}
              (res_name: string)
              (lemma_name: string)
              (nexpr:A):
    TemplateMonad@{t u} unit :=
    e <- tmEval cbv nexpr ;;
      ast <- tmQuote e ;;
      cast <- compileNExpr [] ast ;;
      let '(params, c) := cast in
      (* TODO: params must be >0 *)
      c' <- tmEval cbv c ;; (* extra cbv to fold nats *)
         (* definition with resuting NExpr *)
         def <- tmDefinition res_name c' ;;
         (* lemma *)
         a_params <- build_param_list params ;;
         let param_idx := List.map tRel (iota 0 (length params)) in
         let a_exp := tApp ast param_idx in
         a_c <- tmQuote c' ;;
             let lemma_concl := tApp (tConst "NExpr_term_equiv" []) [a_params; a_c; a_exp] in
             let lemma_ast := build_forall' params lemma_concl in
             (tmBind (tmUnquoteTyped Prop lemma_ast)
                     (fun lemma_body => tmLemma lemma_name lemma_body
                                             ;;
                                             tmReturn tt)).

  Run TemplateProgram (reifyNExp "Ex1_def" "Ex1_lemma" Ex1).
  Next Obligation.
    unfold NExpr_term_equiv.
    intros.
    compute.
    f_equal.
  Qed.

  Print Ex1_def.
  Check Ex1_lemma.

End Reify.
