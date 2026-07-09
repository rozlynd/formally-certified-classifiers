Require Import List String Orders MSets ZArith Arith.
Require Import Coq.Program.Equality.
Import ListNotations Lia.

From RFXP Require Export FloatUtils.

(* String utils *)

Module StringOT : UsualOrderedType
    with Definition t := string :=
    String_as_OT.

Module StringOTF : UsualOrderedTypeFull
    with Definition t := string :=
    OT_to_Full StringOT.

Module StringSet : Sets
    with Module E := StringOT :=
    MSetList.Make StringOT.

Module StringSetProperties := OrdProperties StringSet.
Module StringSetMoreProperties := MSets.MSetFacts.WFactsOn StringOT StringSet.


Section StringEnumerations.

    Import StringSet.

    Definition string_enum (s : StringSet.t) : Type := { x : string | In x s }.

End StringEnumerations.


(* List utils *)

Section ListInit.

    Context {A : Type} (f : nat -> A).

    Fixpoint init_aux (n : nat) (acc : list A) : list A :=
        match n with
        | 0 => acc
        | S n' => init_aux n' (f n' :: acc)
        end.

    Definition init (n : nat) :=
        init_aux n [].

    Lemma init_aux_length : forall (n : nat) (acc : list A),
        length (init_aux n acc) = n + length acc.
    Proof.
        induction n as [| n' IH ]; intros; simpl;
            try reflexivity;
        rewrite IH; simpl; lia.
    Qed.

    Theorem init_length : forall (n : nat),
        length (init n) = n.
    Proof. now intros; unfold init; rewrite init_aux_length. Qed.

    Theorem init_0 :
        init 0 = [].
    Proof. reflexivity. Qed.

    Lemma init_aux_acc : forall (n : nat) (acc : list A),
        init_aux n acc = init_aux n [] ++ acc.
    Proof.
        induction n as [| n' IH ]; intros; simpl;
            try reflexivity;
        now rewrite IH, IH with (acc := [ f n' ]), <- app_assoc.
    Qed.

    Theorem init_S : forall (n : nat),
        init (S n) = init n ++ [ f n ].
    Proof.
        unfold init; induction n as [| n' IH ]; intros;
            try reflexivity;
        rewrite IH, <- app_assoc; simpl;
        now rewrite init_aux_acc.
    Qed.

    Theorem init_nth_error_None : forall (n i : nat),
        n <= i ->
        nth_error (init n) i = None.
    Proof. now intros; rewrite nth_error_None, init_length. Qed.

    Theorem init_nth_error_Some : forall (n i : nat),
        i < n ->
        nth_error (init n) i = Some (f i).
    Proof.
        induction n as [| n' IH ]; intros i H; inversion H;
        rewrite init_S.
        -   rewrite nth_error_app2, init_length, Nat.sub_diag;
            now rewrite ? init_length.
        -   rewrite nth_error_app1, IH;
            now rewrite ? init_length.
    Qed.

End ListInit.

Section ListMisc.

    Theorem forallb_map : forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
        forallb p (map f l) = forallb (fun x => p (f x)) l.
    Proof.
        intros; induction l as [| x l IH ]; now simpl; rewrite ? IH.
    Qed.

    Theorem existsb_map : forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
        existsb p (map f l) = existsb (fun x => p (f x)) l.
    Proof.
        intros; induction l as [| x l IH ]; now simpl; rewrite ? IH.
    Qed.

    Theorem forallb_ext : forall (A : Type) (p q : A -> bool) (l : list A),
        (forall x, p x = q x) -> forallb p l = forallb q l.
    Proof.
        intros; induction l as [| x l IH ]; now simpl; rewrite ? H, ? IH.
    Qed.

    Theorem existsb_ext : forall (A : Type) (p q : A -> bool) (l : list A),
        (forall x, p x = q x) -> existsb p l = existsb q l.
    Proof.
        intros; induction l as [| x l IH ]; now simpl; rewrite ? H, ? IH.
    Qed.

    Theorem existsb_nexists : forall (A : Type) (p : A -> bool) (l : list A),
        existsb p l = false <-> forall x, In x l -> p x = false.
    Proof.
        intros A p l; split.
        -   intros H1 x H2; destruct (p x) eqn:Heq; try reflexivity;
            cut (existsb p l = true);
                [ intro abs; rewrite abs in H1; discriminate |];
            apply existsb_exists; now exists x.
        -   intros H; destruct (existsb p l) eqn:Heq; try reflexivity;
            apply existsb_exists in Heq as (x & H1 & H2);
            rewrite (H _ H1) in H2; discriminate.
    Qed.

    Theorem forallb_nforall : forall (A : Type) (p : A -> bool) (l : list A),
        forallb p l = false <-> exists x, In x l /\ p x = false.
    Proof.
        intros A p l; split.
        -   intros H; induction l as [| x l IH ]; try (now inversion H);
            apply andb_false_iff in H as [Hp | Hind].
            +   exists x; split; [now left | apply Hp].
            +   destruct IH as (y & H); try apply Hind;
                exists y; split; [now right | apply H].
        -   intros (x & H1 & H2);
            destruct (forallb p l) eqn:Heq; try reflexivity;
            rewrite forallb_forall in Heq;
            now rewrite Heq in H2.
    Qed.


    Theorem filter_map_swap : forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
        filter p (map f l) = map f (filter (fun x => p (f x)) l).
    Proof.
        intros A B f p l; induction l as [| x l IH ]; try reflexivity;
        simpl; destruct (p (f x)); now rewrite IH.
    Qed.

End ListMisc.


(* Non-empty lists *)

Section NonEmptyList.

    Variable (A : Type).

    Inductive nelist :=
    | necons (x : A) (l : list A).

End NonEmptyList.

Arguments necons {A}.

Section NonEmptyListMap.

    Context {A B : Type} (f : A -> B).

    Definition nemap (l : nelist A) : nelist B :=
        match l with
        | necons x q => necons (f x) (map f q)
        end.

End NonEmptyListMap.


(* Finite types *)

Section Fin.

    Inductive fin : nat -> Type :=
    | F1 {n : nat} : fin (S n)
    | FS {n : nat} : fin n -> fin (S n).

    Fixpoint to_nat {n : nat} (p : fin n) : nat :=
        match p with
        | F1 => 0
        | FS p => S (to_nat p)
        end.

    Definition to_fin : forall {n : nat} (i : nat), fin n + { ~ i < n }.
        refine (fix to_fin {n : nat} {struct n} :=
            match n return forall (i : nat), fin n + { ~ i < n } with
            | 0 => fun i => inright _
            | S n => fun i =>
                match i return fin (S n) + { ~ i < S n } with
                | 0 => inleft F1
                | S i =>
                    match to_fin i with
                    | inleft p => inleft (FS p)
                    | inright _ => inright _
                    end
                end
            end
        );
        lia.
    Defined.

    Theorem to_nat_lt {n : nat} :
        forall (p : fin n), to_nat p < n.
    Proof.
        induction p;
        [   apply Nat.lt_0_succ
        |   simpl; now apply -> Nat.succ_lt_mono ].
    Qed.

    Theorem to_nat_to_fin {n : nat} :
        forall (p : fin n), to_fin (to_nat p) = inleft p.
    Proof.
        induction p as [| n p IH ]; try reflexivity;
        simpl; now rewrite IH.
    Qed.

    Theorem to_fin_to_nat {n : nat} :
        forall (i : nat) (p : fin n), to_fin i = inleft p -> to_nat p = i.
    Proof.
        induction n as [| n IH ]; intros i p H; try (now inversion p);
        dependent destruction p.
        -   destruct i; try reflexivity;
            simpl in H; destruct (@to_fin n i); inversion H.
        -   destruct i; try (now inversion H);
            simpl in H; destruct (@to_fin n i) eqn:Heqi;
                try (now inversion H);
            simpl; f_equal; apply IH; now inversion H.
    Qed.

    Theorem to_nat_inj {n : nat} :
        forall (m p : fin n), to_nat m = to_nat p -> m = p.
    Proof.
        intros m p H; cut (@inleft (fin n) (~ to_nat m < n) m = inleft p);
        [   intro H'; now inversion H'
        |   now rewrite <- to_nat_to_fin, H, -> to_nat_to_fin ].
    Qed.

    Theorem to_fin_lt {n : nat} :
        forall (i : nat) (p : fin n), to_fin i = inleft p -> i < n.
    Proof.
        intros i p H; apply to_fin_to_nat in H;
        rewrite <- H; now apply to_nat_lt.
    Qed.


    Definition to_nat' {n : nat} (p : fin n) : { i : nat | i < n } :=
        exist _ (to_nat p) (to_nat_lt p).

    Definition to_fin' {n : nat} : { i : nat | i < n } -> fin n.
        refine (fun '(exist _ i q) =>
            match @to_fin n i with
            | inleft p => p
            | inright _ => _
            end
        );
        lia.
    Defined.

    Theorem to_fin_pi' {n : nat} :
        forall (i : nat) (p q : i < n), to_fin' (exist _ i p) = to_fin' (exist _ i q).
    Proof.
        intros i; simpl; destruct (to_fin i);
        try reflexivity; contradiction.
    Qed.

    Theorem to_nat_to_fin' {n : nat} :
        forall (p : fin n), to_fin' (to_nat' p) = p.
    Proof. intro p; unfold to_nat', to_fin'; now rewrite to_nat_to_fin. Qed.

    Theorem to_fin_to_nat' {n : nat} :
        forall (i : nat) (q : i < n), to_nat (to_fin' (exist _ i q)) = i.
    Proof.
        intros i q; destruct (@to_fin n i) as [ p |] eqn:Heqi; try lia;
        cut (to_nat p = i); try (now apply to_fin_to_nat);
        intro E; rewrite <- E; simpl; now rewrite Heqi.
    Qed.


    Fixpoint lift {n : nat} (i : fin n) : fin (S n) :=
        match i with
        | F1 => F1
        | FS i => FS (lift i)
        end.

    Fixpoint liftn {p : nat} (n : nat) : fin p -> fin (n + p) :=
        match n return fin p -> fin (n + p) with
        | 0 => fun i => i
        | S n => fun i => lift (liftn n i)
        end.

End Fin.


Module Type FinSig.
    Parameter n : nat.
End FinSig.

(* definitions of compare and eq_dec not extracted? mysterious *)
Module FinOT (S : FinSig) : UsualOrderedType
    with Definition t := fin S.n.

    Definition t := fin S.n.
    Definition eq := @Logic.eq t.
    Definition lt := fun m p => (@to_nat S.n m < @to_nat S.n p)%nat.
    Definition compare := fun m p => @to_nat S.n m ?= @to_nat S.n p.

    Program Instance eq_equiv : Equivalence eq.

    Program Instance lt_irreflexive : Irreflexive lt.
    Next Obligation. unfold lt; intros p H; lia. Defined.

    Program Instance lt_transitive : Transitive lt.
    Next Obligation. unfold lt in *; lia. Defined.

    Program Instance lt_strorder : StrictOrder lt.

    Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
    Next Obligation. unfold lt; intros m m' Hm p p' Hp; now rewrite Hm, Hp. Defined.


    Theorem compare_spec (m p : fin S.n) : CompareSpec (m = p) (lt m p) (lt p m) (compare m p).
    Proof.
        unfold lt, compare;
        assert (H := PeanoNat.Nat.compare_spec (to_nat m) (to_nat p));
        inversion H as [HEq | HLt | HGt]; clear H; constructor;
        try assumption; now apply to_nat_inj.
    Defined.

    Definition eq_dec (m p : fin S.n) : { m = p } + { m <> p }.
    Proof.
        destruct (PeanoNat.Nat.eq_dec (to_nat m) (to_nat p)) as [HEq | HNeq].
        -   left; now apply to_nat_inj.
        -   right; intro abs; now rewrite abs in HNeq.
    Defined.

End FinOT.

Module FinOTF (S : FinSig) : UsualOrderedTypeFull
    with Definition t := fin S.n.
    Module FOT := FinOT S.
    #[warnings="-parsing"] Include OT_to_Full FOT.
End FinOTF.


Module Type FinSetOn (S : FinSig) <: Sets
    with Definition E.t := fin S.n
    with Definition E.eq := @Logic.eq (fin S.n).

    Include Sets
        with Definition E.t := fin S.n
        with Definition E.eq := @Logic.eq (fin S.n).

    Parameter all : t.
    Parameter compl : t -> t.
    Parameter init : (elt -> bool) -> t.
    Parameter shrink : (t -> bool) -> t -> t.

    Axiom In_all : forall (i : elt), In i all.
    Axiom In_compl : forall (s : t) (i : elt), In i (compl s) <-> ~ In i s.
    Axiom In_init : forall (p : elt -> bool) (i : elt), In i (init p) <-> p i = true.

    Axiom shrink_spec1 : forall (p : t -> bool) (s : t),
        Subset (shrink p s) s.

    Axiom shrink_spec2 : forall (p : t -> bool) (s : t),
        p s = true -> p (shrink p s) = true.

    Axiom shrink_spec3 : forall (p : t -> bool),
        (forall (s1 s2 : t), Subset s1 s2 -> p s1 = true -> p s2 = true) ->
        forall (s1 s2 : t),
            p s1 = true -> Subset s2 (shrink p s1) -> p s2 = true -> Equal s2 (shrink p s1).

    Global Parameter compl_compat : Proper (Equal ==> Equal) compl.

End FinSetOn.

Module Type FinSet := FinSig <+ FinSetOn.

Module MakeFinSetOn (S : FinSig) : FinSetOn S.

    Module X := FinOT S.
    Include MSetList.Make X.

    Local Program Fixpoint all_below (n : nat) : t + { ~ n <= S.n } :=
        match n with
        | 0 => inleft empty
        | S n =>
            match to_fin n with
            | inleft p =>
                match all_below n with
                | inleft s => inleft (add p s)
                | inright _ => inright _
                end
            | inright _ => inright _
            end
        end.
    Solve All Obligations with lia.

    Lemma In_all_below : forall (n : nat), n <= S.n ->
        exists (s : t), all_below n = inleft s /\
            forall (i : elt), to_nat i < n -> In i s.
    Proof.
        induction n as [| n IH ]; intros Hn.
        -   exists empty; split; try reflexivity;
            intros i H; inversion H.
        -   destruct IH as (s & H1 & H2); try lia;
            destruct (@to_fin S.n n) as [p |] eqn:Heqn; try lia;
            exists (add p s); split;
                try (simpl; now rewrite Heqn, H1);
            intros i Hi; inversion Hi; apply add_spec;
                try (right; now apply H2);
            left; apply to_nat_inj; apply to_fin_to_nat in Heqn; lia.
    Qed.

    Program Definition all :=
        match all_below S.n with
        | inleft t => t
        | inright _ => _
        end.
    Solve All Obligations with lia.

    Theorem In_all : forall (i : elt), In i all.
    Proof.
        intros i; unfold all;
        destruct (In_all_below S.n (le_n S.n)) as (s & H1 & H2);
        rewrite H1; apply H2, to_nat_lt.
    Qed.

    Theorem all_spec : forall (i : elt), In i all <-> True.
    Proof. intros; split; try auto; intro; apply In_all. Qed.


    Definition compl (s : t) : t := diff all s.

    Theorem In_compl : forall (s : t) (i : elt), In i (compl s) <-> ~ In i s.
    Proof. intros s i; unfold compl; rewrite diff_spec, all_spec; tauto. Qed.


    Local Program Fixpoint init_aux (filt : elt -> bool) (n : nat) : t + { ~ n <= S.n } :=
        match n with
        | 0 => inleft empty
        | S n =>
            match to_fin n with
            | inleft p =>
                match init_aux filt n with
                | inleft s =>
                    if filt p then
                        inleft (add p s)
                    else
                        inleft s
                | inright _ => inright _
                end
            | inright _ => inright _
            end
        end.
    Solve All Obligations with lia.

    Lemma init_aux_spec : forall (filt : elt -> bool) (n : nat) (s : t) (x : fin S.n),
        init_aux filt n = inleft s -> (In x s <-> filt x = true /\ to_nat x < n).
    Proof.
        intros filt; induction n as [| n IH ]; intros s x H; simpl in H.
        -   inversion H; now split.
        -   destruct (to_fin n) as [p |] eqn:Hn; try discriminate H.
            destruct (init_aux filt n) as [s' |] eqn:Hs'; try discriminate H.
            destruct (filt p) eqn:Hp; inversion H; split; intros H2.
            +   apply add_spec in H2 as [H2 | H2].
                *   apply to_fin_to_nat in Hn; subst; split; auto.
                *   assert (H3 : filt x = true /\ to_nat x < n) by (now apply IH with s');
                    destruct H3; split; auto.
            +   destruct H2 as (H2 & H3); apply add_spec; inversion H3.
                *   left; rewrite <- H4, to_nat_to_fin in Hn; now inversion Hn.
                *   right; now apply IH.
            +   assert (H3 : filt x = true /\ to_nat x < n) by (subst s; now apply IH with s');
                destruct H3; split; auto.
            +   specialize IH with s x; lapply IH; try (now rewrite H1).
                assert (H3 : to_nat x <> n).
                {
                    intros abs; rewrite <- abs, to_nat_to_fin in Hn;
                    inversion Hn; subst x; now rewrite Hp in H2.
                }
                intros H4; apply H4; destruct H2; split; try lia; auto.
    Qed.

    Program Definition init (filt : elt -> bool) : t :=
        match init_aux filt S.n with
        | inleft s => s
        | inright _ => False_rect _ _
        end.
    Solve All Obligations with lia.

    Theorem In_init : forall (p : elt -> bool) (i : elt), In i (init p) <-> p i = true.
    Proof.
        intros p i; unfold init;
        destruct (init_aux p S.n) eqn:H; try lia;
        apply init_aux_spec with (x := i) in H; split; intros H1;
            try (now apply H);
        apply H; split; [assumption | apply to_nat_lt].
    Qed.


    Local Fixpoint shrink_aux (p : t -> bool) (s : t) (i : nat) : t + { S.n < i }.
        refine (
            match i with
            | 0 => inleft s
            | S i =>
                match @to_fin S.n i with
                | inleft k =>
                    let s' :=
                        let s' := remove k s in
                        if p s' then
                            s'
                        else
                            s
                    in
                    match shrink_aux p s' i with
                    | inleft r => inleft r
                    | inright _ => inright _
                    end
                | inright _ => inright _
                end
            end); lia.
    Defined.

    Lemma shrink_aux_spec1 :
        forall (p : t -> bool) (s : t),
            shrink_aux p s 0 = inleft s.
    Proof. reflexivity. Qed.

    Lemma shrink_aux_spec2 :
        forall (p : t -> bool) (s r : t) (i : nat) (q : i < S.n),
            p (remove (to_fin' (exist _ i q)) s) = true ->
                shrink_aux p (remove (to_fin' (exist _ i q)) s) i = inleft r ->
                shrink_aux p s (S i) = inleft r.
    Proof.
        intros p s r i q H1 H2; simpl;
        destruct (to_fin i) eqn:Ei; try lia;
        replace (to_fin' (exist _ i q)) with f in *;
            try (apply to_nat_inj, to_fin_to_nat; now rewrite to_fin_to_nat');
        now rewrite H1, H2.
    Qed.

    Lemma shrink_aux_spec3 :
        forall (p : t -> bool) (s r : t) (i : nat) (q : i < S.n),
            p (remove (to_fin' (exist _ i q)) s) = false ->
                shrink_aux p s i = inleft r ->
                shrink_aux p s (S i) = inleft r.
    Proof.
        intros p s r i q H1 H2; simpl;
        destruct (to_fin i) eqn:Ei; try lia;
        replace (to_fin' (exist _ i q)) with f in *;
            try (apply to_nat_inj, to_fin_to_nat; now rewrite to_fin_to_nat');
        now rewrite H1, H2.
    Qed.

    Program Definition shrink p s :=
        match shrink_aux p s S.n with
        | inleft r => r
        | inright _ => False_rect _ _
        end.
    Solve All Obligations with Lia.lia.

    Lemma shrink_aux_Subset : forall (p : t -> bool) (i : nat) (q : i <= S.n) (s r : t),
        shrink_aux p s i = inleft r -> Subset r s.
    Proof.
        intros p i; induction i as [| i IH ]; intros q s r H;
            try (now inversion H);
        simpl in H; destruct (to_fin i) as [k |] eqn:Hi; try lia;
        destruct (p (remove k s)) eqn:Hp.
        -   destruct (shrink_aux p (remove k s) i) eqn:Hs; inversion H;
            intros x Hx; cut (In x (remove k s));
            [ intros Hrem; now apply remove_spec in Hrem
            | apply IH with (r := r); try lia; now subst r ].
        -   destruct (shrink_aux p s i) eqn:Hs; inversion H;
            apply IH; try lia; now subst r.
    Qed.

    Theorem shrink_spec1 : forall (p : t -> bool) (s : t),
        Subset (shrink p s) s.
    Proof.
        intros; apply shrink_aux_Subset with (p := p) (i := S.n); try lia;
        unfold shrink; now destruct (shrink_aux p s S.n); try lia.
    Qed.

    Lemma shrink_aux_sat :forall (p : t -> bool) (i : nat) (q : i <= S.n) (s r : t),
        shrink_aux p s i = inleft r -> p s = true -> p r = true.
    Proof.
        intros p i; induction i as [| i IH ]; intros q s r H;
            try (now inversion H);
        simpl in H; destruct (to_fin i) as [k |] eqn:Hi; try lia;
        destruct (p (remove k s)) eqn:Hp.
        -   destruct (shrink_aux p (remove k s) i) eqn:Hs; inversion H;
            intros Ht; apply IH with (s := remove k s); try lia; now subst r.
        -   destruct (shrink_aux p s i) eqn:Hs; inversion H;
            apply IH; try lia; now subst r.
    Qed.

    Theorem shrink_spec2 : forall (p : t -> bool) (s : t),
        p s = true -> p (shrink p s) = true.
    Proof.
        intros; apply shrink_aux_sat with (p := p) (s := s) (i := S.n); try lia;
        unfold shrink; now destruct (shrink_aux p s S.n); try lia.
    Qed.

    Lemma shrink_aux_cut : forall (p : t -> bool) (i : nat) (q : i <= S.n) (s r : t) (x : elt),
        shrink_aux p s i = inleft r -> In x r -> to_nat x < i ->
            exists (c : t), Subset r c /\ p (remove x c) = false.
    Proof.
        intros p i; induction i as [| i IH ]; intros q s r x Hr Hx Hlt; try lia;
        pose proof shrink_aux_Subset _ _ q _ _ Hr as Hsubr;
        destruct (Nat.eq_dec (to_nat x) i) as [Hi | Hi];
        simpl in Hr; destruct (to_fin i) as [k |] eqn:Hk; try lia;
            try (replace x with k in *; [| apply to_nat_inj, to_fin_to_nat; now rewrite Hi ]);
        destruct (p (remove k s)) eqn:Hrem.
        -   destruct (shrink_aux p (remove k s) i) as [r' |] eqn:Hr'; inversion Hr; subst r'.
            apply shrink_aux_Subset in Hr'; try lia;
            now apply Hr', remove_spec in Hx.
        -   exists s; split; try assumption.
        -   destruct (shrink_aux p (remove k s) i) as [r' |] eqn:Hr'; inversion Hr; subst r';
            destruct IH with (remove k s) r x; try lia; try assumption;
            now eexists.
        -   destruct (shrink_aux p s i) as [r' |] eqn:Hr'; inversion Hr; subst r';
            destruct IH with s r x; try lia; try assumption;
            now eexists.
    Qed.

    Theorem shrink_spec3 : forall (p : t -> bool),
        (forall (s1 s2 : t), Subset s1 s2 -> p s1 = true -> p s2 = true) ->
        forall (s1 s2 : t),
            p s1 = true -> Subset s2 (shrink p s1) -> p s2 = true -> Equal s2 (shrink p s1).
    Proof.
        (* It suffices to prove [Subset (shrink p s1) s2].
         * Let [In x (shrink p s1)]. There exists a [c] such that [Subset (shrink p s1) c]
         * and [p (remove x c) = false].
         * If [~ In x s2] then [Subset s2 (remove x c))] and by monotonicity [p (remove x c) = true].
         * This is absurd therefore [In x s2]. *)
        intros p Hmono s1 s2 Hs1 HSubset Hs2;
        cut (Subset (shrink p s1) s2);
            try (intros; split; now auto);
        intros x HIn;
        unfold shrink in *; destruct (shrink_aux p s1 S.n) as [r |] eqn:Er; try lia;
        destruct shrink_aux_cut with p S.n s1 r x as (c & Hc & Hrem);
            try lia; try assumption; try (now apply to_nat_lt);
        destruct (mem x s2) eqn:Hmem; try (now apply mem_spec);
        exfalso; cut (Subset s2 (remove x c));
        [ intros abs; now rewrite Hmono with s2 (remove x c) in Hrem
        | intros y Hy; apply remove_spec; split; try auto;
          intros abs; subst x; apply mem_spec in Hy; now rewrite Hy in Hmem ].
    Qed.


    Global Instance compl_compat : Proper (Equal ==> Equal) compl.
    Proof.
        intros s1 s2 HEs x; rewrite 2 In_compl;
        split; intros H abs; now apply H, HEs.
    Qed.

End MakeFinSetOn.

Module MakeFinSet (S : FinSig) : FinSet with Definition n := S.n.
    Definition n := S.n.
    Module F := MakeFinSetOn S.
    Include F.
End MakeFinSet.

Module FinSetProperties (Import FS : FinSet).
    
    Module P := OrdProperties FS.
    Import P P.P.

    Theorem compl_compl : forall (s : t), Equal (compl (compl s)) s.
    Proof.
        intros s x; split; intro H.
        -   rewrite 2 In_compl in H; now destruct (In_dec x s).
        -   now rewrite 2 In_compl.
    Qed.

    Theorem Subset_compl :
        forall (s1 s2 : t),
            Subset s1 s2 <-> Subset (compl s2) (compl s1).
    Proof.
        intros s1 s2; split; intros HS x Hx.
        -   apply In_compl; intro abs;
            apply In_compl in Hx; apply Hx, HS, abs.
        -   destruct (In_dec x s2) as [| HN ]; try trivial.
            apply In_compl, HS, In_compl in HN; contradiction.
    Qed.

End FinSetProperties.


(* a reflexivity proof in Feature breaks if I remove this?? *)
Export StringSetMoreProperties.