Require Import Coq.Strings.String.
Require Import Template.All.
Require Import Switch.Switch.
Require Import Coq.Lists.List.

Import MonadNotation.
Import ListNotations.

Require Import NExpr.

Set Universe Polymorphism.
Set Printing Universes.

Example Ex1 (a b c x: nat) := 2 + (fun x' => a*x'*x' + b*x' + c) x.

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

  Fixpoint compileNExpr (a_n:term): TemplateMonad NExpr :=
    let inat :=  {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} in
    match a_n with
    | (tConstruct inat 0 [])
      => tmReturn (NConst 0)
    | (tApp (tConstruct inat 1 []) [e]) =>
      d_e <- compileNExpr e ;;
          tmReturn (match d_e with
                    | NConst v => NConst (v+1)
                    | o => NPlus o (NConst 1)
                    end)
    | (tApp (tConst bfun []) [ a_a ; a_b]) =>
      d_a <- compileNExpr a_a ;;
          d_b <- compileNExpr a_b ;;
          match parse_NOp_Name bfun with
          | Some n_Add => tmReturn (NPlus d_a d_b)
          | Some n_Sub => tmReturn (NMinus d_a d_b)
          | Some n_Mul => tmReturn (NMult d_a d_b)
          | None => tmFail ("Unknown binary function" ++ bfun)
          end
    | (tLambda _ (tInd inat []) b_n) =>  b_t <- compileNExpr b_n  ;; tmReturn (NLam b_t)
    | tRel n => tmReturn (NVar n)
    | _ => tmFail ("Unsupported NExpr" ++ (string_of_term a_n))
    end.

  Definition reifyNExp@{t u} {A:Type@{t}}
             (res_name: string)
             (lemma_name: string)
             (nexpr:A):
    TemplateMonad@{t u} unit :=
    nn <- tmQuote nexpr ;;
       match nn with
       | tConst name [] =>
         e <- tmEval (unfold "Ex1") nexpr ;; (* TODO: strip `name` up to last '.' *)
           ast <- tmQuote e ;;
           c <- compileNExpr ast ;;
           c' <- tmEval cbv c ;;
           def <- tmDefinition res_name c' ;;
           tmPrint e ;;
           tmPrint c' ;;
           tmReturn tt
       | _ => tmFail "unexpected parameter type"
       end.

  Run TemplateProgram (reifyNExp "Ex1_def" "Ex1_lemma" Ex1).

  Print Ex1_def.

End Reify.
