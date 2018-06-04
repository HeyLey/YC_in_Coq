Import Nat.

Require Import fl.cfg.Definitions.
Require Import fl.int.Base2.
Require Import fl.cfg.Derivation.

Require Import List.

Module Base.
  Import ListNotations.

  Import Definitions Derivation.
  Import Base2.Base.

  Context {Tt Vt: Type}.

  Inductive ext_der {Tt Vt} (G : (@grammar Tt Vt)) : (list symbol) -> (list symbol) -> Prop :=
    | refl (p : list symbol) : ext_der G p p
    | inDer A p (in_der : (der G A p)): ext_der G [Vs A] p.

  Inductive SPPF_node : Type :=
  | mk_terminal_node : Tt  -> nat -> nat -> SPPF_node
  | mk_epsilon_node: nat -> nat -> SPPF_node
  | mk_nonterminal_node : Vt  -> nat -> nat -> SPPF_node
  | mk_intermediate_node :  @phrase Tt Vt -> nat -> nat -> SPPF_node.

  Inductive valid_parent : SPPF_node -> Type :=
  | mk_nonterminal_node_parent v from to : valid_parent (mk_nonterminal_node v from to)
  | mk_intermediate_node_parent p from to : valid_parent (mk_intermediate_node p from to).

  Inductive packed_SPPF_node : Type :=
  | mk_packed_node1 : SPPF_node -> packed_SPPF_node
  | mk_packed_node2 : SPPF_node -> SPPF_node -> packed_SPPF_node.

  Inductive SPPF_rel : Type :=
  | mk_rel : forall p : SPPF_node, (valid_parent p) -> packed_SPPF_node -> SPPF_rel.

  Definition SPPF := list SPPF_rel.

  Definition SPPF_rel_to_nodes (r : SPPF_rel) : list SPPF_node :=
    match r with
    | mk_rel p v n => match n with
                       | mk_packed_node1 n1 => [p; n1]
                       | mk_packed_node2 n1 n2 => [p; n1; n2]
                       end
    end.

  Definition get_nodes (sppf : SPPF) : list SPPF_node :=
     flat_map SPPF_rel_to_nodes sppf.

  Inductive sppf_der (sppf: SPPF) :  SPPF_node -> (@phrase Tt SPPF_node) -> Prop :=
  |  reflDer s :  sppf_der sppf s [Vs (V s)]
  |  terDer (t : Tt) (from : nat) (to : nat) : sppf_der sppf (mk_terminal_node t from to) [Ts (T t)]
  |  epsilonDer (from : nat) (to : nat) : sppf_der sppf (mk_epsilon_node from to) []
  |  mkRel1 p (vp : valid_parent p) ch1 w1 : In (mk_rel vp (mk_packed_node1 ch1)) sppf ->
                          (sppf_der sppf ch1 w1) -> sppf_der sppf p w1
  |  mkRel2 p (vp : valid_parent p) ch1 ch2 w1 w2 : In (mk_rel vp (mk_packed_node2 ch1 ch2)) sppf ->
                                 (sppf_der sppf ch1 w1) -> (sppf_der sppf ch2 w2) -> sppf_der sppf p (w1 ++ w2).


  Definition SPPF_rel_to_rule (r : SPPF_rel) : (@rule Tt SPPF_node) :=
    match r with
    |  mk_rel p v n => match n with
                       | mk_packed_node1 n1 => R (V p) [Vs (V n1)]
                       | mk_packed_node2 n1 n2 => R (V p) [Vs (V n1); Vs (V n2)]
                       end
    end.

  Definition SPPF_node_to_rule (n : SPPF_node) : list (@rule Tt SPPF_node) :=
    match n with
    | mk_terminal_node t from to => [R (V n) [Ts (T t)]]
    | mk_epsilon_node from to => [R (V n) []]
    | mk_nonterminal_node v from to => []
    | mk_intermediate_node p from to => []
    end.

  Definition SPPF_to_grammar1 (s : SPPF) : (@grammar Tt SPPF_node) :=
     flat_map SPPF_node_to_rule (get_nodes s).

  Definition SPPF_to_grammar2 (s : SPPF) : (@grammar Tt SPPF_node) :=
     map SPPF_rel_to_rule s.

  Definition SPPF_to_grammar (s : SPPF) : (@grammar Tt SPPF_node) :=
     (SPPF_to_grammar1 s) ++ (SPPF_to_grammar2 s).

  Lemma in_node n r (sppf : SPPF):
  (In n (get_nodes sppf)) -> (In r (SPPF_node_to_rule n)) ->
  (In r (SPPF_to_grammar sppf)).
  Proof.
    intros inH1 inH2.
    apply in_or_app.
    left.
    unfold SPPF_to_grammar1.
    set (get_nodes sppf) as ns in *.
    induction ns.
    contradiction.
    simpl in inH1.
    destruct inH1.
    { simpl.
      apply in_or_app.
      left.
      rewrite H.
      exact inH2.
    }
    { simpl.
      apply in_or_app.
      right.
      apply IHns.
      exact H.
    }
  Qed.

  Lemma in_rel rel (sppf : SPPF):
  (In rel sppf) ->
  (In (SPPF_rel_to_rule rel) (SPPF_to_grammar sppf)).
  Proof.
    intros inH1.
    apply in_or_app.
    right.
    induction sppf.
    contradiction.
    destruct inH1.
    - left; rewrite H; reflexivity.
    - right; apply IHsppf; apply H.
  Qed.

  Theorem app_eq1 {A} (l: list A): l = [] ++ l ++ [].
    simpl.
    induction l.
    reflexivity.
    simpl.
    rewrite <- IHl.
    reflexivity.
  Qed.

  Theorem app_eq2 {A} (l1 l2: list A): l1 ++ l2 = [] ++ l1 ++ l2.
    reflexivity.
  Qed.

  Theorem app_eq3 {A} (l1 l2: list A): l1 ++ l2  = l1 ++ l2 ++ [].
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Theorem in_rel_impl_in_node (sppf : SPPF) rel (n : SPPF_node):
    In rel sppf -> In n (SPPF_rel_to_nodes rel) ->
    In n (get_nodes sppf).
  Proof.
    intros inH1 inH2.
    induction sppf.
    contradiction.
    destruct inH1.
    {
      apply in_or_app.
      left.
      rewrite H.
      exact inH2.
    }
    { apply in_or_app.
      right.
      apply IHsppf.
      exact H.
    }
  Qed.


  Theorem trans0 (sppf : SPPF) (n : SPPF_node) (p : phrase)
          (i : In n (get_nodes sppf)) (d : (sppf_der sppf n p)) :
    der (SPPF_to_grammar sppf) (V n) p.
  Proof.
    revert i.
    induction d.
    { intro. apply vDer. }
    { intro inH.
      apply rDer.
      apply in_node with (n := mk_terminal_node t from to).
      exact inH.
      simpl.
      left.
      auto.
    }
    { intro inH.
      apply rDer.
      apply in_node with (n := mk_epsilon_node from to).
      exact inH.
      simpl.
      left.
      auto.
    }
    { intro inH.
      rewrite app_eq1.
      apply replN with (B := V ch1).
      rewrite <- app_eq1.
      apply rDer.
      apply in_rel with (rel := (mk_rel vp (mk_packed_node1 ch1))).
      exact H.
      apply IHd.
      apply in_rel_impl_in_node with (rel := (mk_rel vp (mk_packed_node1 ch1))).
      exact H.
      simpl.
      right.
      left.
      reflexivity.
    }
    {
      intro inH.
      rewrite app_eq2.
      apply replN with (B := V ch1).
      rewrite <- app_eq2.
      rewrite app_eq3.
      apply replN with (B := V ch2).
      rewrite <- app_eq3.
      apply rDer.
      simpl.
      apply in_rel in H.
      exact H.
      apply IHd2.
      apply in_rel_impl_in_node with (rel := (mk_rel vp (mk_packed_node2 ch1 ch2))).
      exact H.
      simpl.
      right; right; left; reflexivity.
      apply IHd1.
      apply in_rel_impl_in_node with (rel := (mk_rel vp (mk_packed_node2 ch1 ch2))).
      exact H.
      simpl.
      right; left; reflexivity.
    }
  Qed.

  Inductive top_der {Tt Vt} g : (@var Vt) -> (@phrase Tt Vt) -> Prop :=
  |  refl_top_der S : top_der g S [Vs S]
  |  top_der0 n p (i : In (R n p) g): top_der g n p
  |  top_der1 n n1 p  (d1 : top_der g n1 p) (i : In (R n [Vs n1]) g): top_der g n p
  |  top_der2 n n1 p1 (d1: top_der g n1 p1)
          n2 p2 (d2: top_der g n2 p2) (i : In (@R Tt Vt n [Vs n1; Vs n2]) g):
       top_der g n (p1 ++ p2).

  Theorem eq2 {A} (l: list A): l = l ++ [].
    simpl.
    induction l.
    reflexivity.
    simpl.
    rewrite <- IHl.
    reflexivity.
  Qed.

  Theorem in_rule (sppf : SPPF) r :
    In r (SPPF_to_grammar sppf) ->
    (exists rel, r = SPPF_rel_to_rule rel /\ (In rel sppf)) \/
    (exists n,  In r (SPPF_node_to_rule n) /\ (In n (get_nodes sppf))).
  Proof.
    intro inH.
    apply in_app_or in inH.
    destruct inH.
    { right.
      unfold SPPF_to_grammar1 in H.
      set (get_nodes sppf) as ns in *.
      induction ns.
      contradiction.
      apply in_app_or in H.
      destruct H.
      { exists a.
        split.
        exact H.
        auto.
      }
      { apply IHns in H.
        clear IHns.
        destruct H as [n0 [H0 H1]].
        exists n0.
        split.
        exact H0.
        right; exact H1.
      }
    }
    { left.
      induction sppf.
      contradiction.
      destruct H.
      { exists a.
        auto.
      }
      { apply IHsppf in H.
        clear IHsppf.
        destruct H as [rel [eq i]].
        exists rel.
        split.
        - exact eq.
        - auto.
      }
    }
  Qed.

  Theorem app_eq4 {A} (v1 v2: A): [v1; v2]  = [v1] ++ [v2].
    reflexivity.
  Qed.

  Theorem trans_rev (sppf : SPPF) (n : SPPF_node) (p : phrase):
         top_der (SPPF_to_grammar sppf) (V n) p ->
         (sppf_der sppf n p).
  Proof.
    intro D.
    remember (V n) as a.
    revert n Heqa.
    induction D.
    { intros n Heqa.
      rewrite Heqa.
      apply reflDer.
    }
    { intros n1 Heqa.
      apply in_rule in i.
      destruct i.
      { destruct H as [rel [eq inH]].
        destruct rel.
        destruct p1.
        { simpl in eq.
          rewrite Heqa in eq.
          clear Heqa.
          injection eq as n_eq p_eq.
          rewrite n_eq.
          apply mkRel1 with (vp := v) (ch1 := s).
          exact inH.
          rewrite p_eq.
          apply reflDer.
        }
        { simpl in eq.
          rewrite Heqa in eq.
          injection eq as n_eq p_eq.
          rewrite n_eq.
          rewrite p_eq.
          rewrite app_eq4.
          apply mkRel2 with (vp := v) (ch1 := s) (ch2 := s0).
          exact inH.
          apply reflDer.
          apply reflDer.
        }
      }
      { destruct H as [n2 [inH1 inH2]].
        destruct n2.
        {
          destruct inH1.
          rewrite Heqa in H.
          injection H as n_eq p_eq.
          rewrite <- p_eq.
          rewrite <- n_eq.
          apply terDer.
          contradiction.
        }
        {
          destruct inH1.
          rewrite Heqa in H.
          injection H as n_eq p_eq.
          rewrite <- p_eq.
          rewrite <- n_eq.
          apply epsilonDer.
          contradiction.
        }
        { contradiction.
        }
        { contradiction.
        }
      }
    }
    { intros n0 Heqa.
      apply in_rule in i.
      destruct i.
      { destruct H as [rel [eq inH]].
        destruct rel.
        destruct p1.
        {
          simpl in eq.
          rewrite Heqa in eq.
          clear Heqa.
          injection eq as n_eq p_eq.
          rewrite n_eq.
          apply mkRel1 with (vp := v) (ch1 := s).
          exact inH.
          apply IHD.
          exact p_eq.
        }
        {
          simpl in eq.
          discriminate.
        }
      }
      { destruct H as [n2 [inH1 inH2]].
        destruct n2.
        { simpl in inH1.
          destruct inH1.
          discriminate.
          contradiction.
        }
        { simpl in inH1.
          destruct inH1.
          discriminate.
          contradiction.
        }
        { contradiction. }
        { contradiction. }
      }
    }
    { intros n0 Heqa.
      apply in_rule in i.
      destruct i.
      { destruct H as [rel [eq inH]].
        destruct rel.
        destruct p0.
        { discriminate. }
        { simpl in eq.
          rewrite Heqa in eq.
          clear Heqa.
          injection eq as n0_eq n1_eq n2_eq.
          rewrite n0_eq.
          apply mkRel2 with (vp := v) (ch1 := s) (ch2 := s0).
          exact inH.
          apply IHD1.
          exact n1_eq.
          apply IHD2.
          exact n2_eq.
        }
      }
      { destruct H as [n_s [inH1 inH2]].
        destruct n_s.
        { destruct inH1.
          discriminate.
          contradiction.
        }
        { destruct inH1.
          discriminate.
          contradiction.
        }
        { contradiction. }
        { contradiction. }
      }
    }
  Qed.

  Inductive good_rule {Tt Vt} : (@rule Tt Vt) -> Prop :=
  |  eps_rule s : good_rule (R s [])
  |  term_rule s t : good_rule (R s [Ts (T t)])
  |  one_rule s n0 : good_rule (R s [Vs (V n0)])
  |  two_rule s n1 n2 : good_rule (R s [Vs (V n1); Vs (V n2)]).


  Theorem all_rules_good (sppf : SPPF) r :
    In r (SPPF_to_grammar sppf) -> good_rule r.
  Proof.
    intro H.
    apply in_rule in H.
    destruct H.
    { destruct H as [rel [eq inH]].
      destruct rel.
      destruct p0.
      {
        simpl in eq.
        rewrite eq.
        apply one_rule.
      }
      {
        simpl in eq.
        rewrite eq.
        apply two_rule.
      }
   }
   { destruct H as [n0 [inH1 inH2]].
     destruct n0.
     { simpl in inH1.
       destruct inH1.
       rewrite <- H.
       apply term_rule.
       contradiction.
     }
     { simpl in inH1.
       destruct inH1.
       rewrite <- H.
       apply eps_rule.
       contradiction.
     }
     { contradiction. }
     { contradiction. }
   }
 Qed.

  Theorem app_div {A} (a : A) p1 p2 u w:
    p1 ++ p2 = u ++ [a] ++ w ->
    (exists w1, p1 = u ++ [a] ++ w1 /\ w = w1 ++ p2) \/
    (exists u2 , u = p1 ++ u2 /\ p2 = u2 ++ [a] ++ w).
  Proof.
    revert p1 p2 w.
    induction u.
    {
      intros p1 p2 w eq.
      destruct p1.
      {
       right.
        exists [].
        split.
       - auto.
       - exact eq.
      }
      {
       left.
       injection eq as a_eq w_eq.
       rewrite a_eq.
       exists p1.
       split.
       auto.
       auto.
      }
    }
    {
      intros p1 p2 w eq.
      destruct p1.
      { right.
        exists (a0 :: u).
        split.
        auto.
        auto.
      }
      {
        injection eq as a_eq w_eq.
        apply IHu in w_eq.
        clear IHu.
        destruct w_eq.
        { left.
          destruct H as [w1 [eq1 eq2]].
          exists w1.
          split.
          rewrite a_eq.
          simpl.
          apply f_equal.
          exact eq1.
          exact eq2.
        }
        { right.
          destruct H as [u2 [eq1 eq2]].
          exists u2.
          split.
          rewrite a_eq.
          simpl.
          apply f_equal.
          exact eq1.
          exact eq2.
        }
      }
    }
  Qed.

  Lemma app_eq5 {A} (a b: A) u w :
    [a] = u ++ [b] ++ w -> a = b /\ u = [] /\ w = [].
  Proof.
    intro H.
    destruct u.
    destruct w.
    injection H as H.
    auto.
    discriminate.
    destruct u.
    discriminate.
    discriminate.
  Qed.


  Theorem trans_top_der (sppf : SPPF) (n : SPPF_node) (p : phrase):
    der (SPPF_to_grammar sppf) (V n) p ->
    top_der (SPPF_to_grammar sppf) (V n) p.
  Proof.
    intro D.
    induction D.
    apply refl_top_der.
    apply top_der0.
    exact H.
    remember (u ++ [Vs B] ++ w) as p0.
    clear D1 D2.
    revert B u w Heqp0 v IHD2.
    induction IHD1.
    {
      intros B u w eq v D.
      apply app_eq5 in eq.
      destruct eq as [eq_S [eq_u eq_w]].
      injection eq_S as eq_s.
      rewrite eq_s.
      rewrite eq_u.
      rewrite eq_w.
      rewrite <- app_eq1.
      exact D.
    }
    {
      intros B u w eq v D.
      apply all_rules_good in i as gr.
      remember (R n0 p) as r.
      destruct gr.
      {
        injection Heqr as s_eq p_eq.
        rewrite <- p_eq in eq.
        destruct u.
        discriminate.
        discriminate.
      }
      {
        injection Heqr as s_eq p_eq.
        rewrite <- p_eq in eq.
        apply app_eq5 in eq.
        destruct eq as [eq_S [eq_u eq_w]].
        discriminate.
      }
      {
        injection Heqr as s_eq p_eq.
        rewrite <- p_eq in eq.
        apply app_eq5 in eq.
        destruct eq as [eq_S [eq_u eq_w]].
        rewrite eq_u.
        rewrite eq_w.
        injection eq_S as eq_S.
        rewrite <- app_eq1.
        rename n0 into vn0.
        rename n1 into vn1.
        apply top_der1 with (n1 := B).
        exact D.
        rewrite eq_S in i.
        rewrite s_eq in i.
        exact i.
      }
      {
        injection Heqr as s_eq p_eq.
        rename n0 into vn0.
        rename n1 into vn1.
        rename n2 into vn2.
        rewrite <- p_eq in eq; clear p_eq.
        rewrite app_eq4 in eq.
        apply app_div in eq.
        destruct eq.
        { destruct H as [w1 [eq_n1 eq_w]].
          apply app_eq5 in eq_n1.
          destruct eq_n1 as [eq_S [eq_u eq_w1]].
          rewrite eq_u in *; clear eq_u.
          rewrite eq_w1 in *; clear eq_w1.
          simpl in eq_w.
          rewrite eq_w; clear eq_w.
          rewrite app_nil_l.
          apply top_der2 with (n1 := (V vn1)) (n2 := (V vn2)).
          injection eq_S as eq_S.
          rewrite eq_S.
          exact D.
          apply refl_top_der.
          rewrite <- s_eq.
          exact i.
        }
        { destruct H as [u2 [eq_u eq_n2]].
          apply app_eq5 in eq_n2.
          destruct eq_n2 as [eq_n2 [eq_u2 eq_w]].
          rewrite eq_u2 in *; clear eq_u2 u2.
          rewrite eq_w in *; clear eq_w w.
          rewrite app_nil_r.
          rewrite app_nil_r in eq_u.
          rewrite eq_u; clear eq_u u.
          apply top_der2 with (n1 := (V vn1)) (n2 := (V vn2)).
          apply refl_top_der.
          injection eq_n2 as eq_n2.
          rewrite eq_n2.
          exact D.
          rewrite <- s_eq.
          exact i.
        }
      }
    }
    {
      intros B u w eq v D.
      apply top_der1 with (n3 := n1).
      apply IHIHD1 with (B := B).
      auto.
      auto.
      auto.
    }
    {
      intros B u w eq v D.
      rename n0 into vn0.
      rename n1 into vn1.
      rename n2 into vn2.
      rename p1 into vp1.
      rename p2 into vp2.
      apply app_div in eq.
      destruct eq.
      { destruct H as [w1 [eq1 eq2]].
        rewrite eq2.
        assert (u ++ v ++ w1 ++ vp2 = (u ++ v ++ w1) ++ vp2).
        { rewrite <- app_assoc.
          rewrite <- app_assoc.
          reflexivity.
        }
        rewrite H.
        clear H.
        apply top_der2 with (n1 := vn1) (n2 := vn2).
        apply IHIHD1_1 with (B := B).
        exact eq1.
        exact D.
        exact IHD1_2.
        exact i.
      }
      {
        destruct H as [u2 [eq1 eq2]].
        rewrite eq1; clear eq1 u.
        assert ((vp1 ++ u2) ++ v ++ w = vp1 ++ (u2 ++ v ++ w)).
        {
          rewrite <- app_assoc.
          reflexivity.
        }
        rewrite H; clear H.
        apply top_der2 with (n1 := vn1) (n2 := vn2).
        exact IHD1_1.
        apply IHIHD1_2 with (B := B).
        exact eq2.
        exact D.
        exact i.
      }
    }
  Qed.




  Theorem derivation_equivalence (sppf : SPPF) (n : SPPF_node) (p : phrase)
    (inH : In n (get_nodes sppf)):
    (sppf_der sppf n p) <->
    der (SPPF_to_grammar sppf) (V n) p.
  Proof.
    split.
    {
      intros D.
      apply trans0.
      exact inH.
      exact D.
    }
    {
      intros D.
      apply trans_rev.
      apply trans_top_der.
      exact D.
    }
  Qed.


  Definition symbol_to_sppf_node (s : (@symbol Tt Vt)) : SPPF_node :=
    match s with
    |  Ts (T t) => (mk_terminal_node t 0 0)
    |  Vs (V v) => (mk_nonterminal_node v 0 0)
    end.

  Definition mk_symbol_rel (p: SPPF_node) (vp : valid_parent p) (s : (@symbol Tt Vt)) : SPPF_rel :=
    mk_rel vp (mk_packed_node1 (symbol_to_sppf_node s)).

  Definition mk_rel2 (p : SPPF_node) (vp : valid_parent p)
             (l : SPPF_node) (r : (@symbol Tt Vt)) : SPPF_rel :=
    mk_rel vp (mk_packed_node2 l (symbol_to_sppf_node r)).

  Fixpoint rule_to_sppf_int (n : SPPF_node) (vp : valid_parent n) (rev_p : (@phrase Tt Vt) ) : SPPF :=
     match rev_p with
     |  [] => [mk_rel vp (mk_packed_node1 (mk_epsilon_node 0 0))]
     |  [s] => [mk_symbol_rel vp s]
     |  s1 :: t => let vp2 := mk_intermediate_node_parent t 0 0 in
                     (mk_rel2 vp (mk_intermediate_node t 0 0) s1) :: (rule_to_sppf_int vp2 t)
     end.

  Definition rule_to_sppf (r : (@rule Tt Vt)) : SPPF :=
    match r with
      R (V s) p => rule_to_sppf_int (mk_nonterminal_node_parent s 0 0) (rev p)
    end.


  Definition grammar_to_sppf (g : (@grammar Tt Vt)) : SPPF :=
    flat_map rule_to_sppf g.

  Inductive sppf_s_der (sppf: SPPF) : SPPF_node -> (@phrase Tt Vt) -> Prop :=
  |  s_terDer (t : Tt) (from : nat) (to : nat) :
       sppf_s_der sppf (mk_terminal_node t from to) [Ts (T t)]
  |  s_noterDer (v : Vt) (from : nat) (to : nat) :
       sppf_s_der sppf (mk_nonterminal_node v from to) [Vs (V v)]
  |  s_epsilonDer (from : nat) (to : nat) :
       sppf_s_der sppf (mk_epsilon_node from to) []
  |  s_mkRel1 p (vp : valid_parent p) ch1 w1 : In (mk_rel vp (mk_packed_node1 ch1)) sppf ->
       (sppf_s_der sppf ch1 w1) -> sppf_s_der sppf p w1
  |  s_mkRel2 p (vp : valid_parent p) ch1 ch2 w1 w2 :
       In (mk_rel vp (mk_packed_node2 ch1 ch2)) sppf ->
       (sppf_s_der sppf ch1 w1) -> (sppf_s_der sppf ch2 w2) -> sppf_s_der sppf p (w1 ++ w2).


(*
  Theorem trans_rev_0 (g : grammar) (v : Vt) (p : phrase)
           (d : (sppf_s_der (grammar_to_sppf g) (mk_nonterminal_node v 0 0) p)) : der g (V v) p.
  Proof.
    remember (mk_nonterminal_node v 0 0) as n.
    remember (grammar_to_sppf g) as sppf.
    revert v Heqn.
    induction d.
    { intros; discriminate. }
    { intros.
      injection Heqn as v_eq.
      rewrite v_eq.
      apply vDer.
    }
    { intros; discriminate. }
    { intros.
      destruct vp.
      {
        admit.
      }
      { discriminate. }
    }
    {

    }
 *)


  Definition node_to_phrase (s: SPPF_node) : (@phrase Tt Vt)  :=
  match s with
  | mk_terminal_node t from to => [Ts (T t)]
  | mk_epsilon_node from to => []
  | mk_nonterminal_node v from to => [Vs (V v)]
  | mk_intermediate_node p from to => p
  end.

  Theorem rule_conversion_prop (g : grammar)  (r : (@rule Tt Vt)):
     In r g ->
     forall rel, In rel (rule_to_sppf r) -> In rel (grammar_to_sppf g).
  Proof.
    intros InH1 rel InH2.
    induction g.
    contradiction.
    simpl.
    apply in_or_app.
    destruct InH1.
    { left.
      rewrite H.
      exact InH2.
    }
    { right.
      apply IHg; apply H.
    }
  Qed.

  Definition is_prefix {A} (pr l : list A) := exists s,  pr ++ s = l.

  Theorem prefix_th a u p0 (g : (@grammar Tt Vt)):
    In (R a p0) g -> is_prefix u p0 ->
    exists p (vp : valid_parent p) pn, In (mk_rel vp pn) (grammar_to_sppf g).

  Theorem trans_rev_1 (g : grammar) (s : SPPF_node) (p u : phrase):
    (derf g u p) ->
    ((exists v, u = [Vs (V v)] /\ s = mk_nonterminal_node v 0 0) \/
     (exists a p0, (In (R a p0) g) /\ (is_prefix u p0) /\ s = mk_intermediate_node u 0 0)) ->
    (sppf_s_der (grammar_to_sppf g) s p).
  Proof.
    intro D.
    induction D.
    {
      intro.
      destruct H.
      {
        destruct H as [v [H1 H2]].
        rewrite H1.
        rewrite H2.
        apply s_noterDer.
      }
      {
        destruct H as [a [p0 [H1 [H2 H3]]]].

      }

      rewrite Hequ.
      destruct s.
      { simpl.
        apply s_terDer.
      }
      { simpl.
        apply s_epsilonDer.
      }
      { simpl.
        apply s_noterDer.
      }
      { simpl.
        admit.
      }
    }
    { intros.
      assert (forall rel, In rel (rule_to_sppf (R A u)) -> In rel (grammar_to_sppf g)).
      apply rule_conversion_prop; exact H; clear H.
      destruct A as [v0].
      admit.
    }
    { intros.
      destruct u.
      { assert (w = []) as EqW.
        { remember [] in D2.
          destruct D2.
          - exact Heql.
          - discriminate.
          - discriminate.
        }
        rewrite EqW.
        clear EqW IHD2.
        rewrite app_nil_r.
        apply IHD1; exact Hequ.
      }
      {

      }
    }
}


End Base.





