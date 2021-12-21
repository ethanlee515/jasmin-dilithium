require import AllCore Distr Int List DInterval IntDiv SDist RealSeries.

require VarMatrix.

clone import VarMatrix as IntMat with type ZR.t = int.

(* -- Basic facts that I can't find in the standard library -- *)

lemma mult_cancel_left (x y1 y2 : real):
    (* Really? *)
    y1 = y2 => x * y1 = x * y2.
proof.
    auto.
qed.

lemma sum_over_bool (f : bool -> real):
    sum (fun b => f b) = f true + f false.
proof.
    print sumE_fin.
    rewrite (sumE_fin _ [true; false]).
    smt().
    smt().
    smt().
    (* Gotta love the triple smt call... *)
qed.

lemma mult_assoc (x y z : real):
    (x * y) * z = x * (y * z).
proof.
    smt().
qed.

lemma ineq_div L R : R > 0%r => L <= R => L / R <= 1%r.
    smt().
qed.

lemma prod_geq0 A B : A > 0%r => B > 0%r => A * B > 0%r.
    smt().
qed.

lemma div_geq0 A B : A >= 0%r => B > 0%r => A / B >= 0%r.
    smt().
qed.

lemma algebraic_fact (A B C D : real) : B > 0%r => D > 0%r => A * B * C / (D * B) = A * C / D.
    smt().
qed.

lemma mult_comm (A B : real) : A * B = B * A.
    smt().
qed.

lemma sum_of_zeros (A B) : A = 0 => B = 0 => A + B = 0.
    move => a_def b_def.
    rewrite a_def b_def.
    auto.
qed.

(* sum lemma, proven with the help of Christian Doczkal *)
lemma sumD1_None (f : 'a option -> real) :
    summable f =>
    sum f = sum (fun y => f (Some y)) + f None.
proof.
  move => sum_f.
  rewrite (sumD1 f None).
  apply sum_f.
  rewrite (sum_partition Some (fun y => f (Some y))).
  exact (summable_inj Some).
  have remove_none : forall x y, (x = y => f None + x = y + f None).
  smt().
  apply remove_none.
  apply eq_sum.
  simplify.
  move => x.
  case (x = None).
  * move => x_eq_none.
    simplify.
    rewrite x_eq_none.
    simplify.
    rewrite sum0.
    auto.
  * move => x_not_none.
    simplify.
    rewrite (sumE_fin _ [oget x]).
    smt().
    smt().
    smt().
qed.

(* -- End basic facts -- *)

type V.
op h : V distr.
axiom h_ll: is_lossless h.
op m : int.
op f : varMatrix distr.
axiom f_ll: is_lossless f.
axiom f_shape: forall z, z \in f <=> getDims z = (m, 1).
op M : real.
axiom M_positive : M > 0%r.
op g (v : V) : varMatrix distr.
axiom g_ll: forall v, is_lossless (g v).
axiom g_shape: forall v z, z \in g v <=> getDims z = (m, 1).

require DBool.

clone import DBool.Biased.

op t = fun good => dunit (if good then Some 0 else None).

print sdist.

op dA = dlet h (fun v =>
    dlet (g v) (fun z =>
        dlet (dbiased ((mu1 f z) / M / (mu1 (g v) z)))
            (fun good => dunit (if good then Some (z, v) else None))
    )
).

lemma dA_dlet1E out :
    mu1 dA out =
    sum (fun v =>
        mu1 h v *
        sum (fun z =>
            mu1 (g v) z *
            sum (fun good =>
                mu1 (dbiased ((mu1 f z) / M / (mu1 (g v) z))) good *
                mu1 (dunit (if good then Some (z, v) else None)) out))).
proof.
    rewrite /dA.
    rewrite dlet1E.
    apply eq_sum => /= v.
    apply mult_cancel_left.

    rewrite dlet1E.
    apply eq_sum => /= z.
    apply mult_cancel_left.

    rewrite dlet1E.
    apply eq_sum.
    auto.
qed.

lemma dA_simpl out :
    mu1 dA out =
    sum (fun v =>
    sum (fun z =>
        mu1 h v *
        mu1 (g v) z *
        (
            mu1 (dbiased ((mu1 f z) / M / (mu1 (g v) z))) true *
            mu1 (dunit (Some (z, v))) out
            +
            mu1 (dbiased ((mu1 f z) / M / (mu1 (g v) z))) false *
            mu1 (dunit None) out
        )
    )).
proof.
    rewrite dA_dlet1E.
    apply eq_sum => /= v.
    rewrite - sumZ.
    simplify.
    apply eq_sum => /= z.
    rewrite - mult_assoc.
    apply mult_cancel_left.
    rewrite sum_over_bool => /=.
    auto.
qed.

op bad_event z v = mu1 f z > M * (mu1 (g v) z).
op bad_event_unlikely eps = forall v, mu f (fun z => bad_event z v) < eps.

lemma dA_output_good_supp v z:
    !(bad_event z v) =>
    v \in h =>
    z \in g v =>
    mu1 dA (Some (z, v)) = (mu1 f z / M) * (mu1 h v).
proof.
    move => not_bad v_in_h z_in_gv.
    rewrite /bad_event in not_bad.
    rewrite dA_simpl.
    rewrite dunit1E.
    simplify.

    rewrite (sumD1 _ v).
        apply (summable_fin _ [v]).
        simplify.
        move => x.
        rewrite (sumD1 _ z).
            apply (summable_fin _ [z]).
            move => x0.
            simplify.
            rewrite dunit1E.
            smt().

        simplify.
        case (x = v).
        trivial.
        move => x_ne_v.
        simplify.
        rewrite dunit1E.
        simplify.
        have first_term_zero: b2r (x = v) = 0%r.
            smt().
        rewrite first_term_zero => /=.
        apply sum0_eq.
        simplify.
        move => x0.
        rewrite dunit1E.
        case (x0 = z).
        trivial.
        simplify.
        move => x0_ne_z.
        smt().
    
    simplify.   
    rewrite (sumD1 _ z).
        apply (summable_fin _ [z]).
        move => /= x.
        case (x <> z).
        move => x_ne_z.
        rewrite dunit1E.
        smt().
        smt().
    simplify.
    rewrite dunit1E.
    simplify.

    rewrite dbiased1E => /=.
    
    have clamped_upper: mu1 f z / (M * mu1 (g v) z) <= 1%r.
        apply ineq_div.
        apply prod_geq0.
        apply M_positive.
        smt().
        smt().

    have clamped_lower: mu1 f z / (M * mu1 (g v) z) >= 0%r.
        apply div_geq0.
        case (z \in f).
            smt().
            move => no_sup.
            have not_supp : mu1 f z = 0%r.
                apply supportPn.
                apply no_sup.
            rewrite not_supp.
            auto.

        apply prod_geq0.
        apply M_positive.
        apply z_in_gv.

    have clamped: clamp (mu1 f z / (M * mu1 (g v) z)) = mu1 f z / (M * mu1 (g v) z).
        smt().
    rewrite clamped.

    simplify.

    have gvz_cancelable : mu1 (g v) z > 0%r.
        smt().

    have cancel: mu1 h v * mu1 (g v) z * mu1 f z / (M * mu1 (g v) z) = mu1 h v * mu1 f z / M.
        (* I see that there's an "algebra" tactic but I don't know how to use it *)
        (* It turns my goal into "false" and create contradicting hypothesis *)
        (* I'm not sure how to go from there *)
        (* So I have an "algebraic_fact" lemma but I don't like it *)
        apply algebraic_fact.
        apply z_in_gv.
        apply M_positive.

    rewrite cancel.

    clear cancel.
    clear gvz_cancelable.
    clear clamped clamped_upper clamped_lower.

    have divide_and_conquer : forall (A B C D : real), A = D => B = 0%r => C = 0%r => A + B + C = D.
        auto.

    apply divide_and_conquer.
        smt().

        apply sum0_eq => /=.
        move => x.
        rewrite dunit1E.
        case (x <> z).
            smt().
            smt().

        apply sum0_eq => /=.
        move => x.
        case (x = v).
            smt().
            
            simplify.
            move => x_ne_v.
            apply sum0_eq => /=.
            move => x0.
            rewrite dunit1E.
            smt().
qed.

lemma dA_output_good :
  forall (v : V) (z : varMatrix),
    ! bad_event z v =>
    mu1 dA (Some (z, v)) = mu1 f z / M * mu1 h v.
proof.
  move => v z.
  case (v \in h).
  * move => v_in_h.
    case (z \in g v).
    * move => z_in_gv.
      move => bad_ev.
      apply dA_output_good_supp.
      assumption.
      assumption.
      assumption.
    * move => z_no_supp bad_ev.
      rewrite supportPn in z_no_supp.
      rewrite /bad_event in bad_ev.
      have z_notin_f : mu1 f z = 0%r.
        rewrite z_no_supp in bad_ev.
        simplify bad_ev.
        have bad_ev' : mu1 f z <= 0%r.
          smt().
        have mu1_non_neg : mu1 f z >= 0%r.
          rewrite - massE.
          apply ge0_mass.
          smt().
      rewrite z_notin_f.
      simplify.
      rewrite dA_simpl.
      apply sum0_eq.
      simplify.
      move => v_.
      apply sum0_eq.
      move => z_.
      rewrite dunit1E.
      simplify.
      rewrite dunit1E.
      case (z_ = z).
      * case (v_ = v).
        * move => v_eq z_eq.
          rewrite v_eq.
          rewrite z_eq.
          simplify.
          rewrite z_no_supp.
          auto.
        * smt().
      * smt().
  * move => v_no_supp.
    move => bad_ev.
    rewrite supportPn in v_no_supp.
    rewrite v_no_supp.
    simplify.
    rewrite dA_simpl.
    apply sum0_eq.
    simplify.
    move => v_.
    apply sum0_eq.
    move => z_.
    rewrite dunit1E.
    simplify.
    rewrite dunit1E.
    case (v_ = v).
    * move => v_eq.
      rewrite v_eq.
      rewrite v_no_supp.
      auto.
    * smt().
qed.

lemma dA_output_bad_supp v z:
    bad_event z v =>
    v \in h =>
    z \in g v =>
    mu1 dA (Some (z, v)) = (mu1 (g v) z) * (mu1 h v).
proof.
    move => bad v_in_h z_in_gv.
    rewrite /bad_event in bad.
    rewrite dA_simpl.
    rewrite dunit1E.
    simplify.

    rewrite (sumD1 _ v).
        apply (summable_fin _ [v]).
        simplify.
        move => x.
        rewrite (sumD1 _ z).
            apply (summable_fin _ [z]).
            move => x0.
            simplify.
            rewrite dunit1E.
            smt().

        simplify.
        case (x = v).
        trivial.
        move => x_ne_v.
        simplify.
        rewrite dunit1E.
        simplify.
        have first_term_zero: b2r (x = v) = 0%r.
            smt().
        rewrite first_term_zero => /=.
        apply sum0_eq.
        simplify.
        move => x0.
        rewrite dunit1E.
        case (x0 = z).
        trivial.
        simplify.
        move => x0_ne_z.
        smt().
    
    simplify.   
    rewrite (sumD1 _ z).
        apply (summable_fin _ [z]).
        move => /= x.
        case (x <> z).
        move => x_ne_z.
        rewrite dunit1E.
        smt().
        smt().
    simplify.
    rewrite dunit1E.
    simplify.

    rewrite dbiased1E => /=.
    
    have unclamped_upper: mu1 f z / (M * mu1 (g v) z) > 1%r.
        have H : forall X Y, X > 0%r => X < Y => 1%r < Y / X.
            smt().
        apply H.
        apply prod_geq0.
        apply M_positive.
        smt().
        smt().
        
    have clamping : clamp (mu1 f z / (M * mu1 (g v) z)) = 1%r.
        smt().
    
    rewrite clamping.
    simplify.        
    have add_cancel_left : forall T1 T2, T1 = 0%r => T2 = 0%r => mu1 h v * mu1 (g v) z + T1 + T2 = mu1 (g v) z * mu1 h v.
        smt().
        
    apply add_cancel_left.
        
    apply sum0_eq.
    simplify.

    move => x.
    rewrite dunit1E.
    case (x <> z).
        smt().
        smt().

    apply sum0_eq => /=.
    move => x.
    case (x = v).
        smt().

        simplify.
        move => x_ne_v.
        apply sum0_eq => /=.
        move => x0.
        rewrite dunit1E.
        smt().
qed.

print dA_output_bad_supp.

lemma dA_output_bad :
  forall (v : V) (z : varMatrix),
    bad_event z v =>
    mu1 dA (Some (z, v)) = mu1 (g v) z * mu1 h v.
proof.
  move => v z.
  case (v \in h).
  * move => v_in_h.
    case (z \in g v).
    * move => z_in_gv.
      move => bad_ev.
      apply dA_output_bad_supp.
      assumption.
      assumption.
      assumption.
    * move => z_no_supp bad_ev.
      rewrite supportPn in z_no_supp.
      rewrite z_no_supp.
      simplify.
      rewrite dA_simpl.
      apply sum0_eq.
      simplify.
      move => v_.
      apply sum0_eq.
      move => z_.
      rewrite dunit1E.
      simplify.
      rewrite dunit1E.
      case (z_ = z).
      * case (v_ = v).
        * move => v_eq z_eq.
          rewrite v_eq.
          rewrite z_eq.
          simplify.
          rewrite z_no_supp.
          auto.
        * smt().
      * smt().
  * move => v_no_supp.
    move => bad_ev.
    rewrite supportPn in v_no_supp.
    rewrite v_no_supp.
    simplify.
    rewrite dA_simpl.
    apply sum0_eq.
    simplify.
    move => v_.
    apply sum0_eq.
    move => z_.
    rewrite dunit1E.
    simplify.
    rewrite dunit1E.
    case (v_ = v).
    * move => v_eq.
      rewrite v_eq.
      rewrite v_no_supp.
      auto.
    * smt().
qed.

lemma dA_output_something :
  forall eps, bad_event_unlikely eps =>
    mu dA (fun x => x <> None) =
      sum (fun v => (mu1 h v) * (
        sum (fun z => if bad_event z v then
          (mu1 (g v) z) else
          (mu1 f z) / M))).
proof.
  move => eps bad_event_eps.
  rewrite muE => //.
  simplify.
  rewrite sumD1_None.
    simplify.
    apply (summable_le (mu1 dA) _).
    * apply summable_mu1.
    * simplify.
      move => x.
      case (x = None).
      * smt().
      * simplify.
        rewrite massE.
        smt().
  simplify.
  have LHS_summable : summable (fun (y : varMatrix * V) => mass dA (Some y)).
    have relabel_fn_comp :
      (fun (y : varMatrix * V) => mass dA (Some y)) = (mass dA) \o Some.
      smt().
    rewrite relabel_fn_comp.
    rewrite summable_inj.
      smt().
    have mass_to_mu : mass dA = mu1 dA.
      apply fun_ext.
      move => x.
      apply massE.
    rewrite mass_to_mu.
    rewrite summable_mu1.
  rewrite sum_pair.
    apply LHS_summable.
  rewrite sum_swap.
    apply LHS_summable.
  apply eq_sum.
  move => v.
  simplify.
  rewrite - sumZ.
  apply eq_sum.
  move => z.
  simplify.
  rewrite massE.
  case (bad_event z v).
  * move => bad_ev.
    rewrite dA_output_bad.
    assumption.
    smt().
  * move => neg_bad_ev.
    rewrite dA_output_good.
    assumption.
    smt().
qed.

lemma dA_output_something_summable_inner :
  forall v,
    summable (fun (z : varMatrix) =>
      if bad_event z v then mu1 (g v) z else mu1 f z / M).
proof.
admitted.

lemma dA_output_something_summable :
  summable (fun (v : V) =>
         mu1 h v *
         sum
           (fun (z : varMatrix) =>
              if bad_event z v then mu1 (g v) z else mu1 f z / M)).
proof.
  admitted.

lemma dA_output_something_lowerbound :
    forall eps, bad_event_unlikely eps =>
    mu dA (fun x => x <> None) >= (1%r - eps) / M.
proof.
  move => eps bad_event_eps.
  print dA_output_something.
  rewrite (dA_output_something eps).
    assumption.
  print ler_sum_pos.
  have first_hop :
    ((sum (fun (v : V) =>
      mu1 h v *
      sum (fun (z : varMatrix) =>
        if bad_event z v then mu1 (g v) z else mu1 f z / M))) >=
    (sum (fun (v : V) =>
      mu1 h v *
      sum (fun (z : varMatrix) =>
        if bad_event z v then mu1 (g v) z else 0%r)))).
    print ler_sum_pos.
    apply ler_sum_pos.
    simplify.
    move => v.
    split.
    * have product_of_positives :
        forall (a b : real), a >= 0%r => b >= 0%r => a * b >= 0%r.
        smt().
      apply product_of_positives.
      search mass.
      rewrite - massE.
      apply ge0_mass.
      search sum.
      apply ge0_sum.
      move => z.
      simplify.
      case (bad_event z v).
      * move => bad_ev.
        rewrite - massE.
        apply ge0_mass.
      * smt().
    move => unused.
    clear unused.
    have left_cancel :
      forall (a b c : real), a >= 0%r => b <= c => a * b <= a * c.
      smt().
    apply left_cancel.
      rewrite - massE.
      apply ge0_mass.
    clear left_cancel.
    apply ler_sum_pos.
    move => z.
    simplify.
    case (bad_event z v).
    * move => bad_ev.
      split.
      * rewrite - massE.
        apply ge0_mass.
      * smt().
    * move => bad_ev.
      split.
      * auto.
      * move => unused.
        have div_cancel :
          forall (a b : real), a > 0%r => b >= 0%r => b / a >= 0%r.
          smt().
        apply div_cancel.
        * apply M_positive.
        * rewrite - massE.
          apply ge0_mass.
    apply dA_output_something_summable_inner.
    apply dA_output_something_summable.
  have second_hop :
    (sum (fun (v : V) =>
      mu1 h v *
      sum (fun (z : varMatrix) =>
        if bad_event z v then mu1 (g v) z else 0%r)) >=
    (1%r - eps) / M).
    admit.
  have le_trans :
    forall (a b c : real), a <= b => b <= c => a <= c.
  smt().
  apply (le_trans _ (sum (fun (v : V) =>
      mu1 h v *
      sum (fun (z : varMatrix) =>
        if bad_event z v then mu1 (g v) z else 0%r))) _).
  assumption.
  assumption.
qed.

lemma dA_output_something_upperbound :
  forall eps, bad_event_unlikely eps =>
  mu dA (fun x => x <> None) >= 1%r / M.
proof.
      admitted.

op dF = dlet h (fun v =>
  dlet f (fun z =>
        dlet (dbiased (1%r / M))
            (fun good => dunit (if good then Some (z, v) else None))
  )
).
    

lemma l4_7: forall eps,
    (forall v, mu f (fun z => bad_event z v) < eps) =>
    ((sdist dA dF < eps / M)
      /\ (mu1 dA None < eps / M)).
proof.
    move => eps mu_bad_event.
    split.

    




module A' = {
  proc main() : (varMatrix * V) option = {
     var result; 
     result <$ dA;
     return result;
  }
}.

(*

module A = {
    proc main() : (varMatrix * V) option = {
        var v, z, result, good;
        v <$ h;
        z <$ (g v);
        good <$ dbiased ((mu1 f z) / M / (mu1 (g v) z));
        if (good) {
            result <- Some (z, v);
        } else {
            result <- None;
        }
        return result;
    }
}.

module F = {
    proc main() : (varMatrix * V) option = {
        var v, z, result, good;
        v <$ h;
        z <$ f;
        good <$ dbiased (1%r / M);
        if (good) {
            result <- Some (z, v);
        } else {
            result <- None;
        }
        return result;
    }
}.

op bad_event z v = mu1 f z > M * (mu1 (g v) z).

lemma lemma4_7: forall eps &m,
    (forall v, mu f (fun z => bad_event z v) < eps) =>
    (* Stronger pointwise claim than statistical distance... *)
    ((forall output, `|Pr[A.main() @ &m : res = output] - Pr[F.main() @ &m : res = output]|
        <= if (exists v z, output = Some (z, v) /\ bad_event z v) then 1%r / M else eps / M)
    (* And probability of A outputs something is at least (1-eps) / M *)
      /\ Pr[A.main() @ &m : res = None] < eps / M).
    

  *)

(* I don't understand rewrite's syntax so here we go... *)
(*
lemma dA_inner_dlet1E v z out:
    mu1
        (dlet
            (dbiased ((mu1 f z) / (M * (mu1 (g v) z))))
            (fun good => dunit (if good then Some (z, v) else None)))
        out
    = sum (fun good =>
        mu1 (dbiased ((mu1 f z) / M / (mu1 (g v) z))) good *
        mu1 (dunit (if good then Some (z, v) else None)) out).
proof.
    rewrite dlet1E.
    simplify.
    auto.
qed.

lemma dA_dlet1E_again v out:
    mu1
        (dlet (g v) (fun z =>
            dlet (dbiased ((mu1 f z) / M / (mu1 (g v) z)))
                (fun good => dunit (if good then Some (z, v) else None))))
        out
    =
    sum (fun z =>
        mu1 (g v) z *
        sum (fun good =>
            mu1 (dbiased ((mu1 f z) / M / (mu1 (g v) z))) good *
            mu1 (dunit (if good then Some (z, v) else None)) out
        )
    ).
proof.
    rewrite dlet1E.
    simplify.
    print dA_inner_dlet1E.
    rewrite dA_inner_dlet1E.
        

        
        
    = mu1 (dbiased ((mu1 f z) / M / (mu1 (g v) z))) good
  *)
