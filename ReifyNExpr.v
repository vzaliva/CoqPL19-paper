Require Import Coq.Strings.String.
Require Import Template.All.
Require Import Switch.Switch.
Require Import Coq.Lists.List.

Import MonadNotation.
Import ListNotations.

Require Import NExpr.
Require Import EvalNExpr.

Definition NExpr_term_equiv (σ: evalContext) (s: nat->nat) (d: NExpr) : Prop :=
  forall (Γ: evalContext) (x:nat), Some (s x) = evalNexp (x :: (σ ++ Γ)) d.

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
  Local Opaque Nat.add Nat.sub Nat.mul.

  Definition varlist:Type := list string.

  Fixpoint compileNExpr (params:varlist) (a_n:term): TemplateMonad (varlist*NExpr) :=
    let inat :=  {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} in
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
    | (tLambda (nNamed n) (tInd inat []) b_n) =>  compileNExpr (n::params) b_n
    | tRel n => tmReturn (params, NVar n)
    | _ => tmFail ("Unsupported NExpr" ++ (string_of_term a_n))
    end.

  Polymorphic Definition reifyNExp@{t u} {A:Type@{t}}
              (res_name: string)
              (lemma_name: string)
              (nexpr:A):
    TemplateMonad@{t u} unit :=
    e <- tmEval cbv nexpr ;;
      ast <- tmQuote e ;;
      cast <- compileNExpr [] ast ;;
      let '(params, c) := cast in
      c' <- tmEval cbv c ;; (* extra cbv to fold nats *)
         (* definition with resuting NExpr *)
         def <- tmDefinition res_name c' ;;
         (* lemma *)
         tmPrint params ;;
         tmPrint c' ;;
         tmReturn tt.

  Run TemplateProgram (reifyNExp "Ex1_def" "Ex1_lemma" Ex1).

  Print Ex1_def.

  Lemma Foo:
    forall a b c,
      NExpr_term_equiv [c;b;a] (Ex1 a b c) Ex1_def.
  Proof.
    intros.
    unfold NExpr_term_equiv.
    intros.
    compute.
  Qed.


End Reify.
