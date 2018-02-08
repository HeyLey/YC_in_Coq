Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop fingraph finfun finset.

Require Import fl.cfg.Base fl.cfg.Definitions fl.cfg.Binarize fl.cfg.Chomsky.
Require Import fl.int.Base2 fl.int.DFA fl.int.ChomskyInduction.

Module Union.
  Import ListNotations Definitions Derivation
         Base Base2 ChomskyInduction.

  Section Big.
    
    Section Definitions. 

      Section Del1.
        
        Variable Tt Vt: Type.

        Inductive labeled_Vt : Type :=
        |  start : labeled_Vt
        |  lV : nat -> @var Vt -> labeled_Vt.

        Definition update_var (n : nat) (v: @var Vt): (@var labeled_Vt) := V (lV n v).
        
        Definition update_symbol (n : nat) (s: @symbol Tt Vt): (@symbol Tt labeled_Vt) :=
          match s with
            | Ts t => Ts t
            | Vs v => Vs (V (lV n v))
          end.
        
        
        Definition update_rule (n : nat) (r : @rule Tt Vt): (@rule Tt labeled_Vt) :=
          match r with
            |  R v p => R (V (lV n v)) (map (update_symbol n) p)
          end.

        Definition update_grammar (n : nat) (g : @var Vt * (@grammar Tt Vt)): @grammar Tt labeled_Vt :=
          match g with
              (st, gr) => (R (V start) [Vs (V (lV n st))]) :: (map (update_rule n) gr)
          end.

        Fixpoint grammar_union (l : list (@var Vt * (@grammar Tt Vt))): @grammar Tt labeled_Vt :=
          match l with
            |  [] => []
            |  (g::t) => update_grammar (length t) g ++ (grammar_union t)
          end.

        (* TODO remove duplicate *)
        Fixpoint to_phrase (w: word): @phrase Tt Vt :=
          match w with
            | s::sx => Ts s :: to_phrase sx
            | _ => []
          end.
        
      End Del1.

      Section Del2.
        
        Variables Tt Vt: Type.
        
        Definition grammar_to_language {Tt Vl : Type} (g : @var Vl * (@grammar Tt Vl)) : language :=
          match g with
              (st, gr) => fun w => (der gr (st) (to_phrase Vl w)) 
          end.                                                  

        Definition tranform_phrase (n : nat) (p : @phrase Tt Vt) : phrase :=
          map (update_symbol n) p.

        
        (* TODO Import*)
        Definition unVar (v: var): Vt := let '(V e) := v in e.

        
        Definition get_n (l : @var (labeled_Vt Vt)) : nat :=
          match l with 
            |  V (start ) => 0
            |  V (lV n _) => S n
          end.

        
        Definition update_grammar_simpl (n : nat) (g : @var Vt * (@grammar Tt Vt)): @grammar Tt (labeled_Vt Vt):=
          match g with
              (st, gr) => (map (update_rule n) gr)
          end.

        Fixpoint grammar_union_simpl (l : list (@var Vt * (@grammar Tt Vt))): @grammar Tt (labeled_Vt Vt) :=
          match l with
            |  [] => []
            |  (g::t) => update_grammar_simpl (length t) g ++ (grammar_union_simpl t)
          end.

      End Del2.
      
    End Definitions. 

    Section Sec.
      
      Context {T V: Type}.

      
      Fixpoint to_word (p: @phrase T V): list ter :=
        match p with
          | Ts x :: sx => x :: to_word sx
          | _ => []
        end.


      Lemma lemma2: forall (w: word), @terminal T V (to_phrase V w).
      Proof.
        intros w.
        induction w.
        - intros s IN; inversion IN.
        - intros s IN.
          inversion IN; auto.
          subst s; exists a; auto.
      Qed.


    End Sec.
    

    Variable Tt Vt: Type.

    Let der := @der Tt.

    Section Util.

      Lemma list_lemma A (a: A) u v l:
        u ++ a :: v = l ->
        length l <> length v.
      Proof.
        intro. 
        have LT : length v < length l.
        { revert u v H.
          induction l.
          - intros. 
            exfalso.
            destruct u.
            discriminate.
            discriminate.
          - intros.
            destruct u.
            simpl in H.
            injection H as H.
            rewrite H0.
            auto.
            simpl in H.
            injection H as H.
            simpl. rewrite ltnS ltnW //. 

            apply (IHl u v H0). }
        
        intro CONTR.
          by rewrite CONTR ltnn in LT. 
      Qed.

      
      Lemma inner_in:
        forall A (a : A) u v w,
          In a (u ++ v ++ w) -> In a v \/ In a (u ++ w).
      Proof.
        intros.
        apply in_app_or in H.
        destruct H.
        right.
        apply in_or_app.
        auto.
        apply in_app_or in H.
        destruct H.
        auto.
        right.
        apply in_or_app.
        auto.
      Qed.

      Lemma inner_in_rev:
        forall A (a : A) u v w, In a v \/ In a (u ++ w) -> In a (u ++ v ++ w).
      Proof.
        intros.
        destruct H.
        apply in_or_app.
        right.
        apply in_or_app.
        left.
        exact H.
        apply in_app_or in H.
        destruct H.
        auto.
        auto.
      Qed.


      
      Lemma app_tranform_phrase:
        forall u v n p,
          u ++ v = tranform_phrase n p ->
          exists u0 v0,
            u0 ++ v0 = p /\
            u = tranform_phrase n u0 /\
            v = @tranform_phrase Tt Vt n v0.
      Proof.
        intros.
        revert p H.  
        induction u.
        - intros.
          exists [], p.
          split.
          auto.
          split.
          auto.
          exact H.
        - intros.
          destruct p.
          discriminate.
          destruct a.
          destruct s.
          + injection H as H.
            assert (H1 := IHu p H0).
            destruct H1 as [u0 H1].
            destruct H1 as [v0 H1].
            clear IHu H0.
            destruct H1.
            destruct H1.
            exists (Ts t :: u0), v0.
            split.
            simpl.
            rewrite H0.
            rewrite H.
            reflexivity.
            split.
            simpl.
            rewrite H1.
            reflexivity.
            exact H2.
          + destruct v0.
            discriminate.
          + destruct v0.
            destruct s.
            discriminate.
            destruct v0.
            injection H as H.
            assert (H1 := IHu p H0).
            destruct H1 as [u1 H1].
            destruct H1 as [v1 H1].
            clear IHu H0.
            exists ((Vs (V v0)) :: u1), v1.
            destruct H1.
            destruct H1.
            split.
            simpl.
            rewrite H0.
            reflexivity.
            split.
            rewrite H.
            simpl.
            rewrite H1.
            reflexivity.
            exact H2.
      Qed.


      
      Lemma trasform_app :
        forall (n : nat) (p1 p2 : @phrase Tt Vt),
          tranform_phrase n (p1 ++ p2) = tranform_phrase n p1 ++ tranform_phrase n p2.
      Proof.
        intros.
        induction p1.
        reflexivity.
        simpl.
        rewrite IHp1; reflexivity.
      Qed.
      
      Lemma tranform_phrase_for_word :
        forall (n : nat) (w : word),
          to_phrase (Tt:=Tt) (labeled_Vt Vt) w =
          tranform_phrase n (to_phrase (Tt:=Tt) Vt w).
      Proof.
        intros.
        induction w.
        simpl.
        reflexivity.
        simpl.
        rewrite IHw.
        reflexivity.
      Qed.
      
    End Util.
    
    Section Definitions2.
      
      (* Let grammar := @grammar Tt Vl *)
      
      
    End Definitions2.


    


    
    Let phrase := @phrase Tt (labeled_Vt Vt).
    Let l_grammar := @grammar Tt (labeled_Vt Vt).


    

    
    Lemma grammar_extention:
      forall (g1 g2 : l_grammar) (v : var) (p : phrase),
        der g2 v p ->
        der (g1 ++ g2) v p.
    Proof.
      intros.
      induction H.
      apply vDer.
      apply rDer.
      apply in_or_app; right.
      apply H.
      apply (replN (B := B)).
      apply IHder1.
      apply IHder2.
    Qed.

    


    Section Name1.
      

      Lemma no_start_in_der:
        forall l n0 v0 (p : phrase),
          der (grammar_union l) (V (lV n0 v0)) p ->
          In (Vs (V (start Vt))) p -> False.
      Proof.
        intros ? ? ? ? H.
        remember (V (lV n0 v0)) as st.
        revert n0 v0 Heqst.
        induction H.
        { intros ? ? EQ IN.
          rewrite EQ in IN.
            by destruct IN. }
        { intros ? ? Heqst IN.
          induction l.
          contradiction.
          apply in_app_or in H.
          destruct H.
          destruct a.
          simpl in H.
          destruct H.
          rewrite Heqst in H.
          discriminate.
          induction g.
          contradiction.
          simpl in H.
          destruct H.
          destruct a.
          destruct v1.
          simpl in H.
          injection H as H.
          clear IHl IHg Heqst H.
          rewrite -H0 in IN; clear H0.
          induction p.
          contradiction.
          destruct IN.
          destruct a.
          discriminate.
          destruct v2.
          discriminate.
          exact (IHp H).
          exact (IHg H).
          exact (IHl H). }
        { intros. 
          apply inner_in in H1.
          destruct H1.
          destruct B.
          destruct l0.
          apply (IHder1 n0 v0 Heqst).
          apply inner_in_rev.
          auto.
          apply (IHder2 n v1).
          reflexivity.
          exact H1.
          apply (IHder1 n0 v0 Heqst).
          apply inner_in_rev.
          right.
          exact H1. }
      Qed.   

      
      (* TODO: fix *)
      Lemma ext_grammar l v (p: phrase):
        der (grammar_union_simpl l) v p ->
        der (grammar_union l) v p. 
      Proof.
        intros.
        induction H.
        - intros.
          apply vDer.
        - intros.
          apply rDer.
          induction l.
          contradiction.
          apply in_app_or in H.
          destruct H.
          clear IHl.
          apply in_or_app.
          left.
          destruct a.
          simpl.
          right.
          exact H.
          apply in_or_app.
          right.
          apply IHl.
          exact H.
        - intros.
          apply (replN (B := B)).
          apply (IHder1).
          apply (IHder2).
      Qed.

      Lemma no_start_in_der_abdtract:
        forall G n0 v0 (p: phrase),
          (forall A l, In (R A l) G -> In (Vs (V (start Vt))) l -> False) ->
          der G (V (lV n0 v0)) p ->
          In (Vs (V (start Vt))) p ->
          False.
      Proof.
        intros ? ? ? ? no_start_rule ? ?.
        remember (V (lV n0 v0)) as st.
        revert n0 v0 Heqst.
        induction H.
        - intros.
          rewrite Heqst in H0.
          destruct H0.
          discriminate.
          contradiction.
        - intros.
          apply (no_start_rule A l H).
          exact H0.
        - intros.
          apply inner_in in H0.
          destruct H0.
          destruct B.
          destruct l.
          apply IHder1 with (n0:=n0) (v0:=v0).
          apply inner_in_rev.
          auto.
          exact Heqst.
          apply IHder2 with (n0:=n) (v0:=v1).
          exact H0.
          reflexivity.
          apply IHder1 with (n0:=n0) (v0:=v0).
          apply inner_in_rev.
          right.
          exact H0.
          exact Heqst.
      Qed.
      
      Lemma no_start_in_ders:
        forall l n0 v0 (p: phrase),
          der (grammar_union_simpl l) (V (lV n0 v0)) p ->
          ~ In (Vs (V (start Vt))) p.
      Proof.
          by intros ? ? ? ? DER IN; apply ext_grammar in DER; eapply no_start_in_der; eauto 2.
      Qed.
      

      Lemma not_start2:
        forall l n0 v0 u w,
          ~ der (grammar_union_simpl l) (V (lV n0 v0)) (u ++ [Vs (V (start Vt))] ++ w).
      Proof.
          by intros ? ? ? ? ? DER; eapply no_start_in_ders; eauto 2; eapply inner_in_rev; eauto 2.
      Qed.
      

      Lemma der_n_is_n_abstract
            g0
            (n0 : nat)
            (v0 : var) 
            (p: phrase):
        der g0 (V (lV n0 v0)) p ->
        (forall n0 v0 n v l, In (R (V (lV n0 v0)) l) g0 -> In (Vs (V (lV n v))) l -> n = n0) ->
        (forall n0 v0 u w, der g0 (V (lV n0 v0)) (u ++ [Vs (V (start Vt))] ++ w) -> False) ->
        forall v n, In (Vs (V (lV n v))) p -> n = n0.
      Proof.
        intros H H_g0 H_st.
        intros v n.
        remember (V (lV n0 v0)) as st.
        revert n0 v0 n v Heqst.
        induction H.
        - intros.
          rewrite Heqst in H.
          destruct H.
          injection H as H.
          auto.
          contradiction.
        - intros.
          rewrite Heqst in H.
          clear Heqst.
          apply (H_g0 n0 v0 n v l).
          exact H.
          exact H0.
        - intros.
          apply inner_in in H1.
          destruct H1.
          destruct B.
          destruct l.
          exfalso.

          apply H_st with (n0 := n0) (v0 := v0) (u := u) (w := w).
          rewrite <- Heqst.
          exact H. 
          
          assert (n = n1).
          apply (IHder2 n1 v2 n v1).
          reflexivity.
          exact H1.
          assert (n1 = n0).
          apply (IHder1 n0 v0 n1 v2).
          exact Heqst.
          apply inner_in_rev.
          auto.
          rewrite <- H3.
          exact H2.
          apply (IHder1 n0 v0 n v1).
          exact Heqst.
          apply inner_in_rev.
          auto.
      Qed.
      
      Lemma der_n_is_n_2:
        forall (l : list (var * grammar))
          (n0 : nat)
          (v0 : var) 
          (p: phrase),
          der (grammar_union_simpl l) (V (lV n0 v0)) p ->
          forall v n, In (Vs (V (lV n v))) p -> n = n0.
      Proof.
        intros ? ? ? ? ? ? ?.
        remember (V (lV n0 v0)) as st.
        revert n0 v0 n v Heqst.
        induction H.
        { intros; rewrite Heqst in H.
            by destruct H; [ injection H as H | ]. }
        { intros; rewrite Heqst in H; clear Heqst. 
          induction l; first by done.
          apply in_app_or in H.
          destruct H; last by auto.
          destruct a as [v1 G]. 
          induction G; first by done.
          destruct H; last by auto.
          destruct a.
          destruct v2.
          simpl in H.
          injection H as H.
          rewrite H in H2.
          rewrite <- H2 in H0.
          clear H IHG IHl H1 H2.
          induction p.
          contradiction.
          destruct H0.
          destruct a.
          discriminate.
          destruct v3.
          injection H as H.
          auto.
          auto. }
        
        { intros.
          apply inner_in in H1.
          destruct H1.
          destruct B.
          destruct l0.
          rewrite Heqst in H; apply not_start2 with (n0 := n0) (v0 := v0) in H. by done.
          

          assert (n = n1).
          apply (IHder2 n1 v2 n v1).
          reflexivity.
          exact H1.
          assert (n1 = n0).
          apply (IHder1 n0 v0 n1 v2).
          exact Heqst.
          apply inner_in_rev.
          auto.
          rewrite <- H3.
          exact H2.
          apply (IHder1 n0 v0 n v1).
          exact Heqst.
          apply inner_in_rev.
          auto. }
      Qed.

      Lemma cut_head:
        forall a l n0 v0 p, 
          length l <> n0 ->
          der (grammar_union_simpl (a :: l)) (V (lV n0 v0)) p ->
          der (@grammar_union_simpl Tt Vt l) (V (lV n0 v0)) p.
      Proof.
        intros a l n0 v0 p NEQ DER.
        remember (V (lV n0 v0)) as st.
        revert n0 v0 NEQ Heqst.
        induction DER.
        - intros.
          apply vDer.
        - intros.
          apply in_app_or in H.
          destruct H.
          exfalso.
          rewrite Heqst in H.
          clear Heqst.
          destruct a.
          induction g.
          contradiction.
          destruct H.
          destruct a.
          destruct v1.
          injection H as H.
          auto.
          auto.
          apply rDer.
          exact H.
        - intros.
          destruct B.
          destruct l0.
          + exfalso.
            rewrite Heqst in DER1.
            apply (no_start_in_ders DER1).  
            apply inner_in_rev.
            auto.
          + apply (replN (B := (V (lV n v1)))).
            apply (IHDER1 n0 v0).
            exact NEQ.
            apply Heqst.
            apply (IHDER2 n v1).
            clear IHDER1 IHDER2.
            assert (n = n0).
            rewrite Heqst in DER1.
            apply (der_n_is_n_2 DER1) with (v := v1) .
            apply inner_in_rev.
            left.
            auto.
            rewrite H.
            exact NEQ.
            reflexivity.
      Qed.
      

    End Name1.
    
    Lemma no_tail: 
      forall s_grammars
        (l : phrase)
        (n : nat)
        (v : @var Vt),
        length s_grammars <= n ->
        In (R (V (lV n v)) l) (grammar_union_simpl s_grammars) ->
        False.
    Proof.
      intros.
      induction s_grammars.
      contradiction.
      apply in_app_or in H0.
      destruct H0.
      - assert (length s_grammars < n).
        auto.
        clear H.
        destruct a.
        induction g.
        contradiction.
        simpl in H0.
        destruct H0.
        + destruct a.
          destruct v1.
          simpl in H.
          injection H as H.
          rewrite H in H1.
            by rewrite ltnn in H1.
        + apply (IHg H).
      - apply IHs_grammars.
        simpl in H. by apply ltnW.
        exact H0.
    Qed.  
    
    Lemma cut_tail:
      forall (g : grammar) (a : @var Vt) (r : list (@var Vt * grammar)) n v p,
        n = length r ->
        der (grammar_union_simpl ((a, g) :: r)) (V (lV n v)) p ->
        der (update_grammar_simpl n (a, g)) (V (lV n v)) p.
    Proof.
      intros.
      remember (V (lV n v)) as st.
      revert n v H Heqst.
      induction H0.
      - intros.
        apply vDer.
      - intros.
        apply in_app_or in H.
        destruct H.
        rewrite H0.
        apply rDer.
        exact H.
        exfalso.
        assert (H1 : length r <= n).
        { by rewrite H0.
        }
        rewrite Heqst in H.
        apply (no_tail H1 H).      
      - intros.
        destruct B.
        destruct l.
        exfalso.
        rewrite Heqst in H0_.
        apply (no_start_in_ders H0_).  
        apply inner_in_rev.
        auto.
        apply (replN (B := (V (lV n0 v1)))).
        apply (IHder1 n v0).
        exact H.
        exact Heqst.
        apply (IHder2 n v1).
        apply H.
        assert (n0 = n).
        rewrite Heqst in H0_.
        apply (der_n_is_n_2 H0_ (v:=v1)).
        apply inner_in_rev.
        auto.
        rewrite H0.
        auto.
    Qed.

    Section Util2.
      
      Lemma update_symbol_is_injective:
        forall n (s1 s2 : @symbol Tt Vt),
          update_symbol n s1 = update_symbol n s2 ->
          s1 = s2.                                         
      Proof.
        intros n s1 s2 EQ.
        destruct s1, s2; simpl in *; try done.
        - by injection EQ as EQ; rewrite EQ.
          destruct v; destruct v0.
            by injection EQ as EQ; rewrite EQ.
      Qed.

    End Util2.

    Lemma not_start_in_update:
      forall G a0 n0 n v A u w,
        A = V (lV n v) ->
        der (update_grammar_simpl n0 (a0,G)) A (u ++ [Vs (V (start Vt))] ++ w) ->
        False.
    Proof.
      intros ? ? ? ? ? ? ? ? EQ DER.
      eapply no_start_in_der_abdtract with (p := (u ++ [Vs (V (start Vt))] ++ w)); eauto; last first.
      { by rewrite EQ in DER; exact DER. }
      { intros ? l IN1 IN2; clear DER.
        induction G; first by done.
        destruct IN1; last by eapply IHG; eauto 2.
        destruct a as [[v0] p].
        injection H as H1 H2.
        rewrite <- H2 in IN2.
        clear IHG H1 H2.
        induction p; first by done.
        destruct IN2; last by eapply IHp; eauto 2.
          by destruct a.
      }
    Qed.


    (** * Forward *)
    (** TODO: comment *)    
    Section Forward.

      
      Lemma same_union_0 :
        forall (G : grammar)
          (vst: var)
          
          (v : var)
          (l : list (var * grammar))
          p,

          der G v p ->
          der (grammar_union (Tt:=Tt) ((vst, G) :: l)) (update_var (length l) v)
              (@tranform_phrase Tt Vt (length l) p).
      Proof.
        intros .
        induction H.
        - destruct A.
          simpl.
          apply vDer.
          
        - apply rDer.
          simpl.
          right.
          apply in_or_app; left.
          induction G.
          simpl in H ; contradiction.
          simpl in H.
          destruct H.
          simpl.
          left.
          rewrite H.
          destruct A.
          simpl.
          reflexivity.
          simpl; right. 
          apply (IHG H).
        - rewrite trasform_app.
          rewrite trasform_app.
          apply (replN (B := (update_var (length l) B))
                       (G := (grammar_union (Tt:=Tt) ((vst, G) :: l)))
                ).
          enough (tr_eq :[Vs (update_var (length l) B)] = (@tranform_phrase Tt Vt (length l) [Vs B])).
          rewrite tr_eq.
          rewrite <- trasform_app.
          rewrite <- trasform_app.
          apply IHder1.
          destruct B.
          simpl.
          reflexivity.
          apply IHder2.     
      Qed.  

      
      (* Let grammar_to_language := @grammar_to_language Tt. *)

      Variable s_grammars: list (@var Vt * @grammar Tt Vt). 

      
      Lemma same_union_forward:
        forall word,
          language_list_union (map (@grammar_to_language _ _) s_grammars) word ->
          grammar_to_language (V(start Vt), grammar_union s_grammars) word.
      Proof.
        intros w H1.
        induction s_grammars.  
        simpl in H1.
        contradiction.
        simpl in H1.
        destruct H1.
        clear IHl.
        destruct a.
        unfold grammar_to_language in H.
        unfold grammar_to_language.
        remember (to_phrase (Tt:=Tt) Vt w) as p.
        have EQ1: to_phrase (Tt:=Tt) (labeled_Vt Vt) w = (tranform_phrase (length l) p).
        { by rewrite Heqp; apply tranform_phrase_for_word. }
        rewrite EQ1.
        have EQ2: tranform_phrase (length l) p = [] ++ (tranform_phrase (length l) p) ++ [].
        { rewrite Heqp.
          simpl.
          rewrite cats0.
          reflexivity. }
        rewrite EQ2.
        apply (replN (B := (V (lV (length l) v)))).
        apply rDer.
        simpl.
        left.
        reflexivity.
        have EQ3: V (lV (length l) v) = update_var (length l) v; first by done.
        rewrite EQ3.
        apply same_union_0.
        exact H.                 
        simpl.
        apply grammar_extention.
        apply IHl.
        apply H.
      Qed.

    End Forward.
    
    (** * Backward *)
    (** TODO: comment *)
    Section Backward.

      Section Section1. 

        Variable G : @grammar Tt Vt.


        Lemma der_n_is_n_siml:
          forall (GS: var * grammar)
            (n0: nat)
            (v0: var) 
            (p: phrase ),
            
            der (update_grammar_simpl n0 GS) (V (lV n0 v0)) p ->
            forall v n, In (Vs (V (lV n v))) p ->
                   n = n0.
        Proof.
          intros.
          apply der_n_is_n_abstract with
          (g0 := (update_grammar_simpl n0 GS))
            (v0 := v0)
            (p := p)
            (v := v).
          - exact H.
          - intros.
            clear v v0 H0 p H.
            destruct GS.
            induction g.
            contradiction.
            destruct H1.
            destruct a.
            destruct v0.
            injection H as H.
            rewrite <- H1 in H2.
            rewrite H in H2.
            clear H H1 IHg.
            induction p.
            contradiction.
            destruct H2.
            destruct a.
            discriminate.
            destruct v3.
            injection H as H.
            auto.
            exact (IHp H).
            exact (IHg H).
          - intros.
            remember (V (lV n1 v1)) as A.
            destruct GS. 
            apply (not_start_in_update HeqA H1).
          - exact H0.
        Qed.
        
        
        Lemma update_grammar_simpl_is_injective:
          forall (a a0 : @var Vt)
            (p : _)
            (n : nat),
            der (update_grammar_simpl n (a0,G)) (V (lV n a)) (tranform_phrase n p) ->
            der G a p.
        Proof.
          intros.
          remember (tranform_phrase n p) as p0.
          remember (V (lV n a)) as A.
          revert a HeqA p Heqp0.
          induction H.
          - intros.
            rewrite HeqA in Heqp0.
            destruct p.
            discriminate.
            destruct p.
            simpl in Heqp0.
            destruct s.
            discriminate.
            destruct v.
            simpl in Heqp0.
            injection Heqp0 as H.
            rewrite H.
            apply vDer.
            discriminate.
          - intros.
            apply rDer.
            induction G.
            contradiction.
            destruct H.
            left.
            destruct a1.
            rewrite HeqA in H.
            destruct v.
            simpl in H.
            injection H as H.
            rewrite H.
            clear A IHg HeqA H.
            rewrite Heqp0 in H0.
            clear Heqp0.
            assert (p0 = p).
            revert p H0.
            induction p0.
            + intros.
              destruct p.
              reflexivity.
              discriminate.
            + intros.
              destruct p.
              discriminate.
              injection H0 as H.
              apply update_symbol_is_injective in H.
              rewrite H.
              assert (p0 = p).
              apply IHp0.
              apply H0.
              rewrite H1.
              reflexivity.
            + rewrite H.
              reflexivity.
            + right.
              apply IHg.
              exact H.
          - intros.
            destruct B.
            destruct l.
            exfalso.
            apply (not_start_in_update HeqA H).
            apply app_tranform_phrase in Heqp0.
            destruct Heqp0 as [u1 H1].
            destruct H1 as [t0 H1].
            destruct H1.
            destruct H2.
            apply app_tranform_phrase in H3.
            destruct H3 as [v1 H3].
            destruct H3 as [w1 H3].
            destruct H3.
            destruct H4.
            rewrite <- H3 in H1.
            clear H3.
            rewrite <- H1.
            assert (n0 = n).
            { rewrite HeqA in H.
              apply (der_n_is_n_siml H) with (v := v0).
              apply inner_in_rev.
              auto.
            }
            apply (replN (B := v0)).
            apply IHder1.
            exact HeqA.
            unfold tranform_phrase.
            rewrite map_cat.

            unfold tranform_phrase in H2.
            rewrite <- H2.
            simpl.
            unfold tranform_phrase in H5.
            rewrite <- H5.
            rewrite H3.
            reflexivity.
            
            apply IHder2.
            rewrite H3; reflexivity.
            exact H4.
        Qed.

      End Section1.
      
      Variable s_grammars: list (@var Vt * @grammar Tt Vt).


      Lemma update_grammar_to_union:
        forall word start G (n : nat),           
          In (start, G) s_grammars ->
          der
            (update_grammar_simpl n (start, G))
            (V (lV n start))
            (to_phrase (Tt:=Tt) (labeled_Vt Vt) word) ->
          language_list_union (map grammar_to_language s_grammars) word.
      Proof.
        intros.
        induction s_grammars; first by done.
        destruct H; [left | right].
        { rewrite H; simpl.
          eapply update_grammar_simpl_is_injective with (a0 := start0) (n := n). 
            by rewrite -tranform_phrase_for_word. }
        { by auto 2. }
      Qed.  

      (* TODO: fix proof *)
      Lemma clean_start:
        forall (p: phrase),
          der (grammar_union s_grammars) (V (start Vt)) p ->
          p = [Vs (V (start Vt))] \/
          exists G a u v, (u ++ (a, G) :: v) = s_grammars /\ der (grammar_union s_grammars) (V (lV (length v) a)) p.
      Proof.
        intros. 
        remember (V (start Vt)) as st in H.
        induction H.
        { by left; rewrite Heqst. }
        { right.
          induction s_grammars; first by done.
          apply in_app_or in H.
          destruct H; [clear IHl0 | ].
          { destruct a as [v G].
            exists G, v, [], l0; split; first by done.
            rewrite Heqst in H.
            destruct H.
            { injection H as H.
              rewrite <- H.
                by apply vDer.
            }
            { exfalso.
              induction G; first by done.
                by destruct H; first destruct a.
            }
          }
          {
            intros. have H1 := IHl0 H.
            clear H IHl0.
            destruct H1 as [G [a1 [u1 [v1 H1]]]].
            exists G, a1, (a::u1), v1.
            destruct H1.
            split.
            rewrite <- app_comm_cons.
            apply f_equal with (f := fun l => a::l).
            auto.
            apply grammar_extention.
            auto.
          }
        }
        {
          assert (H1 := IHder1 Heqst).
          clear IHder1.
          destruct H1.
          assert (B = V (start Vt) /\ u = [] /\ w = []).
          {
            destruct u.
            simpl in H1.
            destruct w.
            injection H1 as H1.
            auto.
            discriminate.
            destruct u.
            discriminate.
            discriminate.
          }
          
          clear H1.
          destruct H2.
          destruct H2.
          rewrite H2.
          rewrite H3.
          simpl.
          assert ((v ++ [])%list = v).
          apply app_nil_r.
          rewrite H4.
          apply IHder2.
          exact H1.
          destruct H1 as [g H1].
          destruct H1 as [a H1].
          destruct H1 as [u0 H1].
          destruct H1 as [v0 H1].
          right.
          exists g, a, u0, v0.
          destruct H1.
          split.
          exact H1.
          apply (replN H2 H0).
        }
      Qed.

      (* TODO: comment *)
      Lemma derivability_without_start_rules:
        forall var (p: phrase),
          var <> V (start Vt) -> 
          der (grammar_union s_grammars) var p ->
          der (grammar_union_simpl s_grammars) var p.
      Proof.
        intros ? ? NEQ DER.
        destruct var0 as [[ |n a]]; first by done.
        remember (V (lV n a)) as st. 
        revert n a NEQ Heqst. 
        induction DER.
        { by intros; apply vDer. }
        { intros.
          apply rDer.
          induction s_grammars; first by done.
          apply in_app_or in H.
          destruct H.
          { destruct a0; clear IHl0.
            apply in_or_app; left.
              by destruct H; [rewrite Heqst in H | ]. }
          { by apply in_or_app; right; apply IHl0. } } 
        { intros.
          apply (replN (B := B)).
          { by apply (IHDER1 n a NEQ Heqst). }
          { destruct B.
            destruct l; last by apply (IHDER2 n0 v0).
            exfalso.
            rewrite Heqst in DER1.
            eapply no_start_in_der; eauto 2.
              by apply inner_in_rev; eauto 2.
          }
        }
      Qed.

      (* TODO: comment *)
      Lemma same_union_backward:
        forall word,
          grammar_to_language (V (start Vt), grammar_union s_grammars) word ->
          language_list_union (map grammar_to_language s_grammars) word.
      Proof.
        intros word DER.
        have H1 := clean_start DER. 
        destruct H1; first by exfalso; destruct word. 
        clear DER; move: H => [g [a [u [v [H H0]]]]].
        apply derivability_without_start_rules in H0; last by done.
        have H1: der (update_grammar_simpl (length v) (a,g)) (V (lV (length v) a)) (to_phrase (Tt:=Tt) (labeled_Vt Vt) word).
        { revert s_grammars H H0.
          induction u.
          { intros ? EQ DER.
            rewrite cat0s in EQ.
            rewrite -EQ in DER.
              by eapply cut_tail; eauto 2.  }
          { intros ? EQ DER.
            destruct s_grammars; first by done.
            apply IHu with (s_grammars := l).
            { rewrite <- app_comm_cons in EQ. 
                by injection EQ as H. }
            { eapply cut_head with (a := p); eauto 2.
                by injection EQ as H; eapply list_lemma; eauto 2. }
          }
        }
        eapply update_grammar_to_union; eauto 2.
          by rewrite -H; apply in_or_app; right.
      Qed.
      
    End Backward.

    (** * Main Theorem *)
    (** TODO: comment *)
    Section MainLemma.

      (* TODO? *)
      Let s_grammar: Type := (@var Vt * @grammar Tt Vt).

      (* TODO: comment *) 
      Variable grammars: list s_grammar.
      
      Let l1 := language_list_union (map grammar_to_language grammars).
      Let l2 := grammar_to_language (V (start Vt), grammar_union grammars).

      Theorem same_union:
        language_eq l1 l2.
      Proof.
        apply mk_laguage_eq.
        - apply same_union_forward.
        - apply same_union_backward.
      Qed.

    End MainLemma.

    Section MainLemma1.

      (* TODO: del *)

      (* Feed tactic -- exploit with multiple arguments.
       (taken from http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/7013) *)
      Ltac feed H :=
        match type of H with
          | ?foo -> _ =>
            let FOO := fresh in
            assert foo as FOO; [|specialize (H FOO); clear FOO]
        end.    

      Lemma H_correct_union:
        forall w ls, 
          @Derivation.language _ _
                               (@grammar_union Tt Vt ls)
                               (V (start Vt))
                               (to_phrase _ w) <->
          exists s_l, @Derivation.language _ _ (snd s_l) (fst s_l) (to_phrase _ w) /\ In s_l ls.
      Proof.
        intros.
        have Lem:
          forall ls w,
            language_list_union [seq grammar_to_language (Tt:=Tt) i | i <- ls] w <->
            exists s_g, In s_g ls /\ Derivation.language s_g.2 s_g.1 (to_phrase _ w).
        {  
          clear. intros T ls w; split; intros H.
          { induction ls; first by done.
            move: H => [H|H].
            - clear IHls.
              exists a; split.
                by left.
                destruct a; simpl in *.
                split; [by done| by apply lemma2].
            - apply IHls in H; clear IHls.
              move: H => [[s g] [EL [DER TER]]].
              exists (s,g); split; [by right | by done].
          }
          { move: H => [[s g] [EL [DER TER]]].
            apply in_split in EL.
            move: EL => [l1 [l2 EQ]].
            rewrite EQ.
            simpl.
            clear EQ.
            induction l1.
            simpl. left; by done.
            simpl in *. by right.
          } 
        }
        
        intros; split; intros.
        { move: H => [DER TER].
          have SU := same_union ls w.
          move: SU => [_ SU2].
          feed SU2; first by done.


          
          apply Lem in SU2.
          move: SU2 => [s_g [EL LANG]].
          exists s_g. split. by done.  by done.
        }
        { move: H => [s_g [LANG EL]].
          have SU := same_union ls w.
          move: SU => [SU1 _].
          feed SU1; first by apply Lem; exists s_g; split. 
          unfold grammar_to_language in SU1.
          unfold language; split.
          - by done.
          - move: LANG => [DER TER].
            clear SU1 DER.
            induction w.
            + by done.
            +
              apply lemma2.
        }
      Qed.      
      
    End MainLemma1.
    
  End Big.
  
End Union.