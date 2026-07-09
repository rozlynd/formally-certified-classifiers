Require Import MSets.

From RFXP Require Import Utils CNF.

Module Type SatSolverRaw.

    Variant ans {n : nat} := SAT (I : assignment (fin n)) | UNSAT.

    Parameter solve : forall {n : nat}, cnf (fin n) -> @ans n.

End SatSolverRaw.

Module Type IsCorrectSatSolver (Import Sat : SatSolverRaw).

    Axiom sat_correct : forall {n : nat} (c : cnf (fin n)) (I : assignment (fin n)),
        solve c = SAT I -> eval_cnf I c = true.

    Axiom unsat_correct : forall {n : nat} (c : cnf (fin n)) (I : assignment (fin n)),
        solve c = UNSAT -> eval_cnf I c = false.

End IsCorrectSatSolver.

Module Type SatSolver := SatSolverRaw <+ IsCorrectSatSolver.


Module Type CCEncoderRaw.

    Parameter encode : forall {m n : nat}, cnf_with_cc (fin m) -> cnf (fin n).

End CCEncoderRaw.

Module Type IsCorrectCCEncoder (Import Enc : CCEncoderRaw).

    Axiom encode_correct : forall {n : nat} (c : cnf_with_cc (fin n)) (I : assignment (fin n)),
        eval_cnf I (encode c) = eval_cnf_with_cc I c.

End IsCorrectCCEncoder.

Module Type CCEncoder := CCEncoderRaw <+ IsCorrectCCEncoder.


Module Type MaxSatSolverRaw.

    Declare Module N : FinSig.

    Declare Module S : Sets
        with Definition E.t := fin N.n
        with Definition E.eq := @eq (fin N.n).

    (* solve [hard clauses] [soft clauses] finds a maximally SAT set of soft clauses *)
    Parameter solve : cnf (fin N.n) -> cnf (fin N.n) -> S.t * assignment (fin N.n).

End MaxSatSolverRaw.

(*
Module MakeMaxSatEval (Import MSat : MaxSatSolverRaw).

    Variant filt := include (X : S.t) | exclude (X : S.t).

    Definition apply_filt (f : filt) :=
        match f with
        | include X => fun n => S.mem n X
        | exclude X => fun n => negb (S.mem n X)
        end.

    Fixpoint filter_elts {A : Type} (f : filt) (c : list A) : S.elt -> list A -> list A :=
        match c with
        | nil => fun _ acc => acc
        | cons cls c => fun n acc =>
            if apply_filt f n then
                filter_elts f c (S n) (cls :: acc)
            else
                filter_elts f c (S n) acc
        end.

    Definition make_cnf (f : filt) (c_hard c_soft : cnf nat) : cnf nat :=
        filter_elts f c_soft 0 c_hard.

    Definition maxsat_eval (I : assignment nat) (f : filt) (c_hard c_soft : cnf nat) :=
        eval_cnf I (make_cnf f c_hard c_soft).


    (* Specification of make_cnf *)

    Lemma filter_elts_correct : forall {A : Type} (f : filt) (c acc : list A) (n : nat) (x : A),
        List.In x (filter_elts f c n acc) <->
            List.In x acc
            \/ exists p, apply_filt f (n + p) = true /\ List.nth_error c p = Some x.
    Proof.
        intros A f c; induction c as [| y c IH ]; intros acc n x; split; intro H;
            try (now left).
        -   destruct H as [H | (p & H1 & H2)]; try assumption;
            rewrite nth_error_nil in H2; discriminate.
        -   simpl in H; destruct (apply_filt f n) eqn:Hf;
            apply IH in H as [H | (p & H1 & H2)];
                try (now left);
                try (rewrite Nat_as_DT.add_succ_comm in H1; right; now exists (S p));
            destruct H;
                try (now left);
            subst y; right; exists 0; now rewrite <- plus_n_O.
        -   simpl; destruct (apply_filt f n) eqn:Hf; apply IH;
            destruct H as [H | (p & H1 & H2)];
                try (now left);
                try (now (left; right));
            destruct p;
                try (now inversion H2; left; left);
                try (simpl in H1; now rewrite <- plus_n_O, Hf in H1);
            right; exists p; rewrite Nat_as_DT.add_succ_comm; now split.
    Qed.


    Theorem make_cnf_spec_include : forall (cls : clause nat) (X : S.t) (c_hard c_soft : cnf nat),
        List.In cls (make_cnf (include X) c_hard c_soft) <->
            List.In cls c_hard \/ exists n, S.In n X /\ List.nth_error c_soft n = Some cls.
    Proof.
        intros; unfold make_cnf; rewrite filter_elts_correct;
        split; intros [H | H];
            try (destruct H as (p & H1 & H2));
            try (simpl in H1);
            try (now left);
            try (right; exists p; split);
            try assumption;
            try (now rewrite <- S.mem_spec);
            try (simpl; now rewrite S.mem_spec).
    Qed.

    Theorem make_cnf_spec_exclude : forall (cls : clause nat) (X : S.t) (c_hard c_soft : cnf nat),
        List.In cls (make_cnf (exclude X) c_hard c_soft) <->
            List.In cls c_hard \/ exists n, ~ S.In n X /\ List.nth_error c_soft n = Some cls.
    Proof.
        intros; unfold make_cnf; rewrite filter_elts_correct;
        split; intros [H | H];
            try (destruct H as (p & H1 & H2));
            try (simpl in H1);
            try (now left);
            try (right; exists p; split);
            try assumption;
            try (rewrite <- S.mem_spec; intro abs; now rewrite abs in H1);
            try (simpl; apply eq_true_not_negb; intro abs; apply H1; now rewrite <- S.mem_spec).
    Qed.

    Theorem maxsat_eval_spec : forall (I : assignment nat) (f : filt) (c_hard c_soft : cnf nat),
        maxsat_eval I f c_hard c_soft = eval_cnf I (make_cnf f c_hard c_soft).
    Proof. reflexivity. Qed.


    (* We may need to remove nats greater than the number of soft clauses in sets *)

    Definition normalize : nat -> S.t -> S.t :=
        fun m => S.filter (fun n => Nat.ltb n m).

    Instance compatb : Proper (S.E.eq ==> S.E.eq ==> Logic.eq) (fun m n => Nat.ltb n m).
        intros n p H; now rewrite H.
    Defined.

    Theorem normalize_spec : forall (n : nat) (X : S.t) (p : nat),
        S.In p (normalize n X) <-> S.In p X /\ p < n.
    Proof.
        intros; unfold normalize; rewrite S.filter_spec;
            try (now apply compatb);
        split; intros (H1 & H2); split;
            now destruct (Nat_as_DT.ltb_spec0 p n).
    Qed.

End MakeMaxSatEval.

Module Type IsCorrectMaxSatSolver (Import MSat : MaxSatSolverRaw).

    Module Import D := MakeMaxSatEval MSat.

    Section Props.

        Variables
            (c_hard c_soft : cnf nat)
            (Xout : S.t)
            (Iin Iout : assignment nat).

        Hypothesis result :
            solve c_hard c_soft = (Xout, Iout).

        Axiom mss_isSAT :
            eval_cnf Iout (make_cnf (include Xout) c_hard c_soft) = true.

        Axiom mss_isMax :
            forall X I, S.Subset Xout X ->
                eval_cnf I (make_cnf (include X) c_hard c_soft) = true ->
                    S.Equal (normalize (length c_soft) X) (normalize (length c_soft) Xout).

    End Props.

End IsCorrectMaxSatSolver.

Module Type MaxSatSolver := MaxSatSolverRaw <+ IsCorrectMaxSatSolver.
*)
