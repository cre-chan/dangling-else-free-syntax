Require Import Lists.List.

Inductive simple_statement :=
| simp .
(*The simple statement does not matter, so it has no condition*)

Inductive expr :=
|e.
(*The same as above*)

Inductive token :=
|EXPR
|STATEMENT
|COND
|ELSE.
(*The token definition*)

Inductive closed_statement :=
|statement(s:simple_statement)
|if_else(e:expr)(s2 s1:closed_statement).
(*closed statement*)

Inductive open_statement :=
| open_simple (s:simple_statement)
| open_if_simple(e:expr)(s:simple_statement)
|open_if(e:expr)(s:open_statement)
|half_closed_if(e:expr)(s1:closed_statement)(s2:open_statement).
(**)

Inductive statement' :=
|open (s:open_statement)
|closed (s:closed_statement).

Inductive eval_simple:simple_statement->(list token)->Prop:=
|uniq_s: eval_simple (simp) (STATEMENT::nil) .

Inductive eval_expr:expr->(list token)->Prop:=
|uniq_e: eval_expr (e) (EXPR::nil).

Inductive eval_closed:closed_statement->(list token)->Prop:=
|eval_closed_simple s s_tokens:
   (eval_simple s s_tokens)->
   eval_closed (statement s) (s_tokens)
(*evals to OPEN_STATEMENT*)
|eval_closed_if_else e s1 s2 e_tokens s1_tokens s2_tokens:
   (eval_expr e e_tokens)->(eval_closed s1 s1_tokens)->(eval_closed s2 s2_tokens)->
   eval_closed (if_else e s1 s2) ((COND::e_tokens)++s1_tokens++(ELSE::s2_tokens)).
(*evals to IF (EXPRESSION) CLOSED_STATEMENT else CLOSED_STATEMENT*)

Inductive eval_open:open_statement->(list token)->Prop:=
|eval_open_simple s s_tokens:
   (eval_simple s s_tokens)->eval_open (open_simple s) s_tokens
|eval_if_simple e s e_tokens s_tokens:
   (eval_simple s s_tokens)->(eval_expr e e_tokens)->
   eval_open (open_if_simple e s) (COND::e_tokens++s_tokens)
(*evals to a IF (EXPRESSION) SIMPLE_STATEMENT *)
|eval_open_if e e_tokens s s_tokens:
   (eval_expr e e_tokens)->(eval_open s s_tokens)->
   eval_open (open_if e s) (COND::e_tokens++s_tokens)
(*evals to a IF (EXPRESSION) OPEN_STATEMENT *)
|eval_half_closed e s1 s2 e_tokens s1_tokens s2_tokens:
   (eval_expr e e_tokens)->(eval_closed s1 s1_tokens)->(eval_open s2 s2_tokens)->
   eval_open (half_closed_if e s1 s2) (COND::e_tokens++s1_tokens++ELSE::s2_tokens).
(*evals to a IF (EXPRESSION) CLOSED_STATEMENT ELSE OPEN_STATEMENT *)

Inductive eval_statement:statement'->(list token)->Prop:=
|eval_open_statement s s_tokens:
   (eval_open s s_tokens)->(eval_statement (open s) s_tokens)
|eval_closed_statement s s_tokens:
   (eval_closed s s_tokens)->(eval_statement (closed s) s_tokens).

Example exm1:
  (eval_open
     (half_closed_if e  (statement simp) (open_if_simple e simp))
     (COND::EXPR::STATEMENT::ELSE::COND::EXPR::STATEMENT::nil)
     ).
Proof.
  apply (eval_half_closed e (statement simp) (open_if_simple e simp)
                          (EXPR::nil) (STATEMENT::nil) (COND::EXPR::STATEMENT::nil)).
  - apply uniq_e.
  - apply (eval_closed_simple _ _).
    apply uniq_s.
  -  apply (eval_if_simple e simp (EXPR::nil) (STATEMENT::nil)).
     apply uniq_s.
     apply uniq_e.
Qed.


Lemma app_inj:forall T (l1 l2 l3:list T),
    (l1++l2)=(l1++l3)->l2=l3.
Proof.
  intros.
  induction l1.
  - simpl in H.
    apply H.
  - simpl in H.
    injection H as H'.
    apply (IHl1 H').
Qed.



Lemma first_equality':forall s s_tokens s' s'_tokens l l',
    (eval_closed s s_tokens)->
    (eval_closed s' s'_tokens)->
    (s_tokens++l=s'_tokens++l') ->
    s_tokens=s'_tokens.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  generalize dependent s'_tokens.
  generalize dependent s'.
  induction H.
  - intros.
    inversion H .
    inversion H0.
    + inversion H4.
      reflexivity.
    + rewrite <- H8 in H1.
      rewrite <- H3 in H1.
      discriminate.
  - intros.
    inversion H2.
    + inversion H4.
      rewrite <- H8 in H3.
      discriminate.
    + destruct e1.
      inversion H4.
      destruct e0.
      inversion H.
      rewrite <- H11 in H3.
      rewrite <- H10 in H8.
      rewrite <- H8 in H3.
      injection H3 as Hs1_head.
      rewrite <- app_assoc in Hs1_head.
      rewrite <- app_assoc in Hs1_head.
      rewrite <- app_comm_cons in Hs1_head.
      rewrite <- app_comm_cons in Hs1_head.
      assert(
          Hs1_head':s1_tokens ++ ELSE :: s2_tokens ++ l = s1_tokens0 ++ ELSE :: s2_tokens0 ++ l'
        ). apply Hs1_head .
      apply (IHeval_closed1 s0 s1_tokens0 H5 _ _) in Hs1_head.
      rewrite Hs1_head.
      rewrite Hs1_head in Hs1_head'.
      apply app_inj in Hs1_head'.
      injection Hs1_head'.
      intro.
      apply (IHeval_closed2 s3 s2_tokens0 H6 _ _) in H3.
      rewrite H3.
      reflexivity.
Qed.

    
Theorem unambiguous_closed:forall s1 s2 tokens,
   (eval_closed s1 tokens)->(eval_closed s2 tokens)->s1=s2.
Proof.
  intros.
  generalize dependent s2.
  generalize dependent tokens.
  induction s1.
  - intros. inversion H.
    inversion H1.
    rewrite <- H4 in H0.
    inversion H0.
    inversion H5.
    destruct s.
    reflexivity.
  - intros.
    inversion H.
    rewrite <- H5 in H0.
    inversion H0.
    + inversion H7.
    + inversion H8.
      inversion H3.
      rewrite <- H13 in H7.
      rewrite <- H15 in H7.
      simpl in H7.
      inversion H7.
      assert(H17':s1_tokens0 ++ ELSE :: s2_tokens0 = s1_tokens ++ ELSE :: s2_tokens).
      apply H17.
      apply (first_equality' s3 s1_tokens0 s1_1 s1_tokens _ _ H9 H4) in H17.
      rewrite H17 in H9.
      apply (IHs1_1 s1_tokens H4 s3) in H9.
      rewrite H9.
      destruct e0.
      rewrite H17 in H17'.
      apply app_inj in H17'.
      injection H17' as H17''.
      rewrite H17'' in H11.
      apply (IHs1_2 s2_tokens H6 _) in H11.
      rewrite H11.
      reflexivity.
Qed.
