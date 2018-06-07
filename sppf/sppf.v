Import Nat.

Require Import fl.cfg.Definitions.
Require Import fl.cfg.Derivation.
Require Import fl.cfg.Chomsky.
Require Import fl.int.Base2.
Require Import fl.int.ChomskyInduction.


Require Import List.

Module Base.
  Import ListNotations.

  Import Definitions Derivation.
  Import Base2.Base.
  Import Chomsky.
  Import ChomskyInduction.

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


  Theorem sppf_der_impl_der (sppf : SPPF) (n : SPPF_node) (p : phrase)
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

  Theorem top_der_impl_sppf_der (sppf : SPPF) (n : SPPF_node) (p : phrase):
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
      apply sppf_der_impl_der.
      exact inH.
      exact D.
    }
    {
      intros D.
      apply top_der_impl_sppf_der.
      apply trans_top_der.
      exact D.
    }
  Qed.

  Inductive chomsky_rule : Type :=
  | chomsky_term (v : (@var Vt)) (t : (@ter Tt)) : chomsky_rule
  | chomsky_bin (v : (@var Vt)) (c1 : (@var Vt)) (c2 : (@var Vt)) : chomsky_rule.

  Definition chomsky_rule_revert (c :  chomsky_rule) : rule :=
    match c with
    | chomsky_term v t => R v [Ts t]
    | chomsky_bin v c1 c2 => R v [Vs c1; Vs c2]
    end.

  Inductive proofed_rule r : Type :=
    p_r ch : r = chomsky_rule_revert(ch) -> proofed_rule r.

  Theorem convert_to_chomsky  (g : grammar) (c : chomsky g) (r : (@rule Tt Vt)) :
    (In r g) -> proofed_rule r.
  Proof.
    intro.
    destruct c as [E [Un [Bn Uf]]].
    destruct r.
    destruct p.
    {
      apply E in H.
      exfalso; apply H; reflexivity.
    }
    destruct p.
    {
      destruct s.
      exists (chomsky_term v t).
      reflexivity.
      exfalso.
      apply (Uf v).
      exists v0.
      exact H.
    }
    {
      destruct p.
      {
        destruct s.
        {
          exfalso.
          assert ([Ts t; s0] = [Ts t]).
          unfold Separate.uniform in Un.
          apply (Un v).
          exact H.
          left.
          reflexivity.
          discriminate.
        }
        destruct s0.
        {
          exfalso.
          assert ([Vs v0; Ts t] = [Ts t]).
          apply (Un v).
          apply H.
          right; left; reflexivity.
          discriminate.
        }
        exists (chomsky_bin v v0 v1).
        reflexivity.
      }
      exfalso.
      unfold Binarize.binary in Bn.
      assert (length ( s :: s0 :: s1 :: p ) <= 2).
      apply (Bn v).
      exact H.
      assert ((s :: s0 :: s1 :: p) = [s; s0; s1] ++ p).
      {
        simpl; reflexivity.
      }
      rewrite H1 in H0.
      rewrite app_length in H0.
      simpl in H0.
      apply le_S_n in H0.
      apply le_S_n in H0.
      apply le_n_0_eq in H0.
      discriminate.
    }
  Qed.

  Definition extract_value r (pr : proofed_rule r) : chomsky_rule :=
    match pr with
          p_r ch eq => ch
    end.

  Fixpoint simplify_grammar_int (g : grammar) (c : chomsky g) (g0 : (@grammar Tt Vt)) :
    (forall r, In r g0 -> In r g) -> list chomsky_rule :=
    match g0 return (forall r, In r g0 -> In r g) -> list chomsky_rule with
    |  [] => (fun f => [])
    |  h::t => (fun f =>
          (extract_value (convert_to_chomsky c (f h (in_eq h t))))
          ::(@simplify_grammar_int g c t (fun r => fun in1 => f r (in_cons h r t in1)))
       )
    end.


  Definition simplify_grammar (g : grammar) (c : chomsky g) : list chomsky_rule :=
    simplify_grammar_int c (fun r => fun i => i).



  Lemma in_chomsky_impl_in_simple_int (g g0: grammar)
                      (c : chomsky g)
                      (r : rule)
                      (IH : In r g0)
                      (in_f :  (forall r, In r g0 -> In r g)):
    exists cr : chomsky_rule,
    In cr (simplify_grammar_int c in_f) /\
    r = chomsky_rule_revert cr.
  Proof.
    induction g0.
    contradiction.
    destruct IH.
    simpl.
    exists (extract_value (convert_to_chomsky (g:=g) c (r:=a) (in_f a (in_eq a g0)))).
    split.
    left.
    reflexivity.
    clear IHg0.
    rewrite <- H.
    remember (convert_to_chomsky (g:=g) c (r:=a) (in_f a (in_eq a g0))) as pr.
    destruct pr.
    simpl.
    exact e.
    apply IHg0 with
        (in_f := (fun (r0 : rule) (in1 : In r0 g0) => in_f r0 (in_cons a r0 g0 in1)))
        in H.
    clear IHg0.
    destruct H as [cr [H0 H1]].
    exists cr.
    split.
    simpl.
    right.
    exact H0.
    exact H1.
  Qed.



  Theorem in_chomsky_impl_in_simple (g :grammar) (c : chomsky g) (r :rule) (IH : In r g):
    exists (cr : chomsky_rule), (In cr (simplify_grammar c) /\ (r = chomsky_rule_revert cr)).
  Proof.
    unfold simplify_grammar.
    apply in_chomsky_impl_in_simple_int.
    exact IH.
  Qed.

  Definition chomsky_rule_to_SPPF_rel (c : chomsky_rule) : SPPF_rel :=
    match c with
    | chomsky_term (V v) (T t) => (mk_rel (mk_nonterminal_node_parent v 0 0)
                                          (mk_packed_node1 (mk_terminal_node t 0 0)))
    | chomsky_bin (V v) (V c1) (V c2) => (mk_rel (mk_nonterminal_node_parent v 0 0)
                                                 (mk_packed_node2
                                                    (mk_nonterminal_node c1 0 0)
                                                    (mk_nonterminal_node c2 0 0)
                                                 )
                                         )
    end.


  Definition chomsky_to_SPPF (l : list chomsky_rule) : SPPF :=
    map chomsky_rule_to_SPPF_rel l.


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


  Definition node_to_phrase (s: SPPF_node) : (@phrase Tt Vt)  :=
  match s with
  | mk_terminal_node t from to => [Ts (T t)]
  | mk_epsilon_node from to => []
  | mk_nonterminal_node v from to => [Vs (V v)]
  | mk_intermediate_node p from to => p
  end.

  Definition chomsky_SPPF (g : grammar) (c : chomsky g) : SPPF :=
    chomsky_to_SPPF (simplify_grammar c).

  Theorem in_r_impl_cr (sg : list chomsky_rule) r
          (H : In r (chomsky_to_SPPF sg)):
    exists cr, In cr sg /\ chomsky_rule_to_SPPF_rel cr = r.
  Proof.
    induction sg.
    contradiction.
    destruct H.
    {
      exists a.
      split.
      auto.
      auto.
    }
    {
      apply IHsg in H.
      clear IHsg.
      destruct H as [cr [H1 H2]].
      exists cr.
      split.
      auto.
      auto.
    }
  Qed.

  Theorem simplify_grammar_revert_int (g g0: grammar) (c : chomsky g) (cr : chomsky_rule)
          (in_f : forall r, In r g0 -> In r g)
          (H1 : In cr (simplify_grammar_int c in_f)):
    exists (r : rule) (H_I : In r g), cr = extract_value (convert_to_chomsky (g:=g) c (r:=r) H_I).
  Proof.
    induction g0.
    contradiction.
    simpl in H1.
    destruct H1.
    { exists a, (in_f a (in_eq a g0)).
      auto.
    }
    { apply IHg0 with (in_f := (fun (r : rule) (in1 : In r g0) => in_f r (in_cons a r g0 in1))).
      exact H.
    }
  Qed.


  Theorem simplify_grammar_revert (g : grammar) (c : chomsky g)
          (cr : chomsky_rule)
          (H1 : In cr (simplify_grammar c)):
    exists (r : rule) (H_I : In r g), cr = (extract_value (convert_to_chomsky c H_I)).
  Proof.
    unfold simplify_grammar in H1.
    apply simplify_grammar_revert_int with (in_f := (fun (r : rule) (i : In r g) => i)).
    exact H1.
  Qed.


  Theorem in_chomsky_SPPF (g : grammar)  (c : chomsky g) rel
          (H : In rel (chomsky_SPPF (g:=g) c)):
    exists cr : chomsky_rule,
      In (chomsky_rule_revert cr) g /\ rel = chomsky_rule_to_SPPF_rel cr.
  Proof.
    unfold chomsky_SPPF in *.
    remember (simplify_grammar (g:=g) c) as sg.
    apply in_r_impl_cr in H.
    destruct  H as [cr [H1 H2]].
    rewrite Heqsg in H1.
    clear Heqsg.
    apply simplify_grammar_revert in H1.
    destruct H1 as [r [H_I HEQ]].
    remember (convert_to_chomsky (g:=g) c (r:=r) H_I) as ct in *.
    destruct ct as [cr1 CR_EQ].
    exists cr1.
    split.
    {
      rewrite <- CR_EQ.
      exact H_I.
    }
    { simpl in HEQ.
      rewrite <- HEQ.
      auto.
    }
  Qed.

  Inductive top_chomsky_der {Tt Vt} g : (@var Vt) -> (@phrase Tt Vt) -> Prop :=
  |  ch_refl_top_der S : top_chomsky_der g S [Vs S]
  |  ch_ter_der n t (i : In (R n [Ts t]) g):  top_chomsky_der g n [Ts t]
  |  ct_two_der n n1 p1 (d1: top_chomsky_der g n1 p1)
         n2 p2 (d2: top_chomsky_der g n2 p2) (i : In (@R Tt Vt n [Vs n1; Vs n2]) g):
       top_chomsky_der g n (p1 ++ p2).


  Theorem convert_to_top_chomsky (g : (@grammar Tt Vt)) (c : chomsky g) a (p : phrase):
    (der g a p) -> top_chomsky_der g a p.
  Proof.
    intro D.
    induction D.
    { apply ch_refl_top_der. }
    {
      apply convert_to_chomsky in H as H0.
      destruct H0.
      destruct ch.
      { injection e as A_eq L_eq.
        rewrite A_eq in *.
        rewrite L_eq in *.
        apply ch_ter_der.
        exact H.
      }
      { injection e as A_eq L_eq.
        rewrite A_eq in *.
        rewrite L_eq in *.
        rewrite app_eq4.
        apply ct_two_der with (n1 := c1) (n2 := c2).
        apply ch_refl_top_der.
        apply ch_refl_top_der.
        exact H.
      }
      exact c.
    }
    { remember (u ++ [Vs B] ++ w) as p0.
      revert u w Heqp0.
      clear D1 D2.
      induction IHD1.
      { intros u w Heqp0.
        apply app_eq5 in Heqp0.
        destruct Heqp0 as [S_eq [u_eq w_eq]].
        rewrite u_eq.
        rewrite w_eq.
        rewrite <- app_eq1.
        injection S_eq as S_eq.
        rewrite S_eq.
        auto.
      }
      { intros u w Heqp0.
        apply app_eq5 in Heqp0.
        destruct Heqp0 as [S_eq [u_eq w_eq]].
        discriminate.
      }
      {
        intros u w Heqp0.
        apply app_div in Heqp0.
        rename n1 into vn1.
        rename n2 into vn2.
        destruct Heqp0.
        {
          destruct H as [w1 [p_eq w_eq]].
          rewrite w_eq; clear w_eq.
          assert (u ++ v ++ w1 ++ p2 = (u ++ v ++ w1) ++ p2).
          { rewrite <- app_assoc.
            rewrite <- app_assoc.
            reflexivity.
          }
          rewrite H; clear H.
          apply ct_two_der with (n1 := vn1) (n2 := vn2).
          apply IHIHD1_1.
          auto.
          auto.
          auto.
        }
        {
          destruct H as [w1 [u_eq p_eq]].
          rewrite u_eq; clear u_eq.
          assert ((p1 ++ w1) ++ v ++ w = p1 ++ (w1 ++ v ++ w)).
          {
            rewrite <- app_assoc.
            reflexivity.
          }
          rewrite H; clear H.
          apply ct_two_der with (n1 := vn1) (n2 := vn2).
          auto.
          apply IHIHD1_2.
          auto.
          auto.
        }

      }
    }
  Qed.

  Theorem in_chomsky_impl_in_SPPF (g : grammar) (c : chomsky g) (r : rule)
          (H_in : In r g):
    exists cr : chomsky_rule,
      In (chomsky_rule_to_SPPF_rel cr) (chomsky_SPPF c) /\ r = chomsky_rule_revert cr.
  Proof.
    apply in_chomsky_impl_in_simple with (c := c) in H_in.
    destruct H_in as [cr [H_IN H_EQ]].
    exists cr.
    unfold chomsky_SPPF.
    set (simplify_grammar (g:=g) c) as sg in *.
    split.
    {
      induction sg.
      contradiction.
      destruct H_IN.
      { left.
        rewrite H.
        reflexivity.
      }
      { right.
        apply IHsg.
        exact H.
      }
    }
    exact H_EQ.
  Qed.


  Theorem top_chomsky_to_SPPF (g : grammar) (c : chomsky g) a (p : phrase):
    (top_chomsky_der g (V a) p) ->
    sppf_s_der (chomsky_SPPF c) (mk_nonterminal_node a 0 0) p.
  Proof.
    intro D.
    remember (V a) as va.
    revert a Heqva.
    induction D.
    { intros a H_EQ.
      rewrite H_EQ.
      apply s_noterDer.
    }
    { intros a H_EQ.
      rewrite H_EQ in i.
      apply in_chomsky_impl_in_SPPF with (c := c) in i.
      destruct i as [cr [IH1 EQ]].
      destruct cr.
      { destruct v as [v].
        injection EQ as a_eq t_eq.
        rewrite t_eq; clear t t_eq.
        destruct t0 as [t0].
        rewrite a_eq.
        simpl in IH1.
        apply s_mkRel1 with
            (vp := mk_nonterminal_node_parent v 0 0)
            (ch1 := mk_terminal_node t0 0 0).
        auto.
        apply s_terDer.
      }
      { destruct v as [v].
        destruct c1 as [c1].
        destruct c2 as [c2].
        simpl in EQ.
        discriminate.
      }
    }
    { intros a H_EQ.
      rewrite H_EQ in i; clear H_EQ.
      apply in_chomsky_impl_in_SPPF with (c := c) in i.
      destruct i as [cr [IH1 EQ]].
      destruct cr.
      { destruct v as [v].
        destruct t as [t].
        discriminate.
      }
      { destruct v as [v].
        simpl in EQ.
        injection EQ as a_EQ n1_EQ n2_EQ.
        rewrite a_EQ in *; clear a a_EQ.
        rewrite n1_EQ in *. clear n1 n1_EQ.
        rewrite n2_EQ in *. clear n2 n2_EQ.
        destruct c1 as [c1].
        destruct c2 as [c2].
        apply s_mkRel2 with
            (vp := mk_nonterminal_node_parent v 0 0)
            (ch1 := mk_nonterminal_node c1 0 0)
            (ch2 := mk_nonterminal_node c2 0 0).
        auto.
        apply IHD1.
        auto.
        apply IHD2.
        auto.
      }
    }
  Qed.

  Theorem sppf_imp_der_rev (g : grammar) (c : chomsky g) a (p : phrase):
    (sppf_s_der (chomsky_SPPF c) (mk_nonterminal_node a 0 0) p) ->
    (der g (V a) p).
  Proof.
    intro D.
    remember (chomsky_SPPF (g:=g) c) as s.
    remember (mk_nonterminal_node a 0 0) as n.
    revert a Heqn.
    induction D.
    { intros a EQ.
      discriminate.
    }
    { intros a EQ.
      injection EQ as v_EQ from_eq to_eq.
      rewrite v_EQ.
      apply vDer.
    }
    { intros a EQ.
      discriminate.
    }
    { intros a Heqn.
      rewrite Heqs in H.
      apply in_chomsky_SPPF in H.
      destruct H as [cr [Hin EQ2]].
      clear IHD.
      destruct cr.
      { destruct v as [v].
        destruct t as [t].
        destruct D.
        { simpl in EQ2.
          injection EQ2 as p_eq vp_eq t_eq from_eq to_eq.
          clear vp_eq.
          rewrite t_eq.
          clear t_eq from_eq to_eq.
          rewrite Heqn in p_eq.
          injection p_eq as a_eq.
          rewrite a_eq.
          apply rDer.
          auto.
        }
        { discriminate. }
        { discriminate. }
        { destruct vp0.
          discriminate.
          discriminate.
        }
        { destruct vp0.
          discriminate.
          discriminate.
        }
      }
      { destruct v as [v].
        destruct c1 as [c1].
        destruct c2 as [c2].
        discriminate.
      }
    }
    { intros a EQ.
      rewrite Heqs in H.
      apply in_chomsky_SPPF in H.
      destruct H as [cr [Hin EQ2]].
      destruct cr.
      { destruct v as [v].
        destruct t as [t].
        discriminate.
      }
      { destruct v as [v].
        destruct c1 as [c1].
        destruct c2 as [c2].
        injection EQ2 as p_eq vp_eq ch1_eq ch2_eq.
        clear vp_eq.
        rewrite p_eq in *; clear p p_eq.
        rewrite ch1_eq in *; clear ch1 ch1_eq.
        rewrite ch2_eq in *; clear ch2 ch2_eq.
        injection EQ as EQ.
        rewrite <- EQ; clear a EQ.
        rewrite app_eq2.
        apply replN with (B := V c1).
        { rewrite <- app_eq2.
          rewrite app_eq3.
          apply replN with (B := V c2).
          apply rDer.
          auto.
          apply IHD2.
          auto.
        }
        { apply IHD1.
          auto.
        }
      }
    }
  Qed.

  Theorem derivation_equivalence_rev (g : grammar) (c : chomsky g) a (p : phrase):
    (sppf_s_der (chomsky_SPPF c) (mk_nonterminal_node a 0 0) p) <->
    der g (V a) p.
  Proof.
    split.
    { intros D.
      apply sppf_imp_der_rev with (c := c).
      auto.
    }
    { intros D.
      apply convert_to_top_chomsky in D.
      apply top_chomsky_to_SPPF.
      exact D.
      auto.
    }
  Qed.

End Base.





