require import AllCore Distr Int List DInterval IntDiv SDist RealSeries.
require VarMatrix.

import StdOrder.RealOrder.

clone import VarMatrix as IntMat with type ZR.t = int.

lemma sum_over_bool (f : bool -> real):
  sum (fun b => f b) = f true + f false.
proof.
rewrite (sumE_fin _ [true; false]) //.
move => -[|] //.
qed.

lemma sumD1_None (f : 'a option -> real) :
  summable f =>
  sum f = sum (fun y => f (Some y)) + f None.
proof.
move => sum_f; rewrite (sumD1 f None) // RField.addrC; congr.
rewrite (sum_partition Some (fun y => f (Some y))).
exact (summable_inj Some).
apply eq_sum => -[|x /=]; 1: by rewrite /= sum0.
rewrite (sumE_fin _ [x]) // /#.
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


op dA = dlet h (fun v =>
  dlet (g v) (fun z =>
    dlet (dbiased ((mu1 f z) / M / (mu1 (g v) z)))
      (fun good => dunit (if good then Some (z, v) else None))
  )
).

lemma dA_ll :
  is_lossless dA.
proof.
rewrite /dA.
apply dlet_ll; 1: apply h_ll.
move => v v_supp /=.
apply dlet_ll; 1: apply g_ll.
move => z z_supp /=.
apply dlet_ll; 1: apply dbiased_ll.
move => ? ? /=.
by apply dunit_ll.
qed.

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
congr.
rewrite dlet1E.
apply eq_sum => /= z.
congr.
rewrite dlet1E.
apply eq_sum => //.
qed.

lemma dA_simpl out :
  mu1 dA out =
  sum (fun v =>
  sum (fun z =>
    mu1 h v *
    mu1 (g v) z * (
      mu1 (dbiased ((mu1 f z) / M / (mu1 (g v) z))) true *
      mu1 (dunit (Some (z, v))) out +
      mu1 (dbiased ((mu1 f z) / M / (mu1 (g v) z))) false *
      mu1 (dunit None) out))).
proof.
rewrite dA_dlet1E.
apply eq_sum => /= v.
rewrite - sumZ => /=.
apply eq_sum => /= z.
rewrite RField.mulrA; congr.
rewrite sum_over_bool => //.
qed.

op bad_event z v = mu1 f z > M * (mu1 (g v) z).
op bad_event_unlikely eps = forall v, mu f (fun z => bad_event z v) <= eps.

lemma dA_output_good_supp v z:
    !(bad_event z v) =>
    v \in h =>
    z \in g v =>
    mu1 dA (Some (z, v)) = (mu1 f z / M) * (mu1 h v).
proof.
move => not_bad v_in_h z_in_gv.
rewrite /bad_event in not_bad.
rewrite dA_simpl.
rewrite dunit1E /=.
rewrite (sumD1 _ v) => /=.
  apply (summable_fin _ [v]) => /= x.
  rewrite (sumD1 _ z) => /=.
    apply (summable_fin _ [z]) => x0 /=.
    rewrite dunit1E => /#.
  case (x = v); 1: trivial.
  move => x_ne_v => //.
  rewrite dunit1E.
  have first_term_zero: b2r (x = v) = 0%r by smt().
  rewrite first_term_zero /=.
  apply sum0_eq => x0 /=.
  rewrite dunit1E.
  case (x0 = z) => /#.
rewrite (sumD1 _ z) => /=.
  apply (summable_fin _ [z]).
  move => /= x.
  case (x = z); 1: by smt().
  move => x_ne_z.
  rewrite dunit1E => /#.
rewrite dunit1E dbiased1E /=.
    
have clamped_upper: mu1 f z / (M * mu1 (g v) z) <= 1%r.
  apply ler_pdivr_mulr.
  apply pmulr_lgt0; 1: by assumption.
  by apply M_positive => //.
  smt().

have clamped_lower: mu1 f z / (M * mu1 (g v) z) >= 0%r.
  apply divr_ge0.
  * case (z \in f); 1: by smt().
    move => no_sup.
    have not_supp : mu1 f z = 0%r.
      apply supportPn.
      by apply no_sup.
    by rewrite not_supp => //.
  * by apply pmulr_rge0; 1: apply M_positive; apply ge0_mu.

have clamped: clamp (mu1 f z / (M * mu1 (g v) z)) = mu1 f z / (M * mu1 (g v) z) by smt().
rewrite clamped /=.

clear clamped clamped_upper clamped_lower.

have cancel: mu1 h v * mu1 (g v) z * mu1 f z / (M * mu1 (g v) z) = mu1 h v * mu1 f z / M.
  field.
  (* How does field actually work...? *)
  apply RField.mulf_neq0.
  apply gtr_eqF.
  apply M_positive.
  apply gtr_eqF.
  apply z_in_gv.
  apply gtr_eqF.
  apply M_positive.
rewrite cancel.
clear cancel.

have divide_and_conquer : forall (A B C D : real), A = D => B = 0%r => C = 0%r => A + B + C = D.
  by auto.

apply divide_and_conquer.
* smt().
* apply sum0_eq => /= x.
  rewrite dunit1E.
  by case (x <> z) => /#.
* apply sum0_eq => /= x.
  case (x = v) => /=; 1: smt().
  move => x_ne_v.
  apply sum0_eq => /= x0.
  by rewrite dunit1E /#.
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
  * move => z_in_gv bad_ev.
    apply dA_output_good_supp; by assumption.
  * move => z_no_supp bad_ev.
    rewrite supportPn in z_no_supp.
    rewrite /bad_event in bad_ev.
    have z_notin_f : mu1 f z = 0%r.
      rewrite z_no_supp in bad_ev.
      (* Following line doesn't work *)
      simplify bad_ev.
      (* How do I use simplify on a hypothesis? *)
      have bad_ev' : mu1 f z <= 0%r.
        smt().
      have mu1_non_neg : mu1 f z >= 0%r.
        rewrite ge0_mu.
      smt().
    rewrite z_notin_f /= dA_simpl.
    apply sum0_eq => v_ /=.
    apply sum0_eq => z_ /=.
    (* How to rewrite all? *)
    rewrite dunit1E dunit1E => /=.
    case (z_ = z); 2: smt().
    case (v_ = v); 2: smt().
    move => v_eq z_eq.
    by rewrite v_eq z_eq /= z_no_supp //.
* move => v_no_supp bad_ev.
  rewrite supportPn in v_no_supp.
  rewrite v_no_supp => /=.
  rewrite dA_simpl.
  apply sum0_eq => v_ /=.
  apply sum0_eq => z_ /=.
  (* How to rewrite all? *)
  rewrite dunit1E dunit1E.
  case (v_ = v); 2: smt().
  move => v_eq.
  by rewrite v_eq v_no_supp //.
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
rewrite dunit1E => /=.
rewrite (sumD1 _ v) /=.
  apply (summable_fin _ [v]) => x /=.
  rewrite (sumD1 _ z) /=.
    apply (summable_fin _ [z]) => x0 /=.
    rewrite dunit1E /#.
  case (x = v); 1: by trivial.
  move => x_ne_v /=.
  rewrite dunit1E /=.
  have first_term_zero: b2r (x = v) = 0%r by smt().
  rewrite first_term_zero => /=.
  apply sum0_eq => x0 /=.
  rewrite dunit1E /#.
rewrite (sumD1 _ z) /=.
  apply (summable_fin _ [z]).
  move => /= x.
  case (x = z); 1: smt().
  rewrite dunit1E /#.
rewrite dunit1E dbiased1E /=.

have unclamped_upper: mu1 f z / (M * mu1 (g v) z) > 1%r.
  have H : forall X Y, X > 0%r => X < Y => 1%r < Y / X by smt().
  apply H; 2: smt().
  apply mulr_gt0; 2: smt().
  apply M_positive.
have clamping : clamp (mu1 f z / (M * mu1 (g v) z)) = 1%r.
  smt().

rewrite clamping /=.
have add_cancel_left :
  forall T1 T2,
    T1 = 0%r => T2 = 0%r => mu1 h v * mu1 (g v) z + T1 + T2 = mu1 (g v) z * mu1 h v.
  smt().
apply add_cancel_left.
* apply sum0_eq => x /=.
  rewrite dunit1E.
  case (x <> z); smt().
* apply sum0_eq => x /=.
  case (x = v); 1: smt().
  move => x_ne_v /=.
  apply sum0_eq => x0 /=.
  by rewrite dunit1E /#.
qed.

lemma dA_output_bad :
  forall (v : V) (z : varMatrix),
    bad_event z v =>
    mu1 dA (Some (z, v)) = mu1 (g v) z * mu1 h v.
proof.
move => v z.
case (v \in h).
* move => v_in_h.
  case (z \in g v).
  * move => z_in_gv bad_ev.
    apply dA_output_bad_supp; by assumption.
  * move => z_no_supp bad_ev.
    rewrite supportPn in z_no_supp.
    rewrite z_no_supp /=.
    rewrite dA_simpl.
    apply sum0_eq => v_ /=.
    apply sum0_eq => z_ /=.
    rewrite dunit1E dunit1E /=.
    case (z_ = z); 2: smt().
    case (v_ = v); 2: smt().
    move => v_eq z_eq.
    by rewrite v_eq z_eq z_no_supp //.
* move => v_no_supp bad_ev.
  rewrite supportPn in v_no_supp.
  rewrite v_no_supp dA_simpl /=.
  apply sum0_eq => v_ /=.
  apply sum0_eq => z_ /=.
  rewrite dunit1E dunit1E /=.
  case (v_ = v); 2: smt().
  move => v_eq.
  by rewrite v_eq v_no_supp //.
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
rewrite muE => // /=.
rewrite sumD1_None => /=.
  apply (summable_le (mu1 dA) _).
  * by apply summable_mu1.
  * smt().
have LHS_summable : summable (fun (y : varMatrix * V) => mu1 dA (Some y)).
  have relabel_fn_comp :
    (fun (y : varMatrix * V) => mu1 dA (Some y)) = (mu1 dA) \o Some.
    smt().
  rewrite relabel_fn_comp.
  rewrite summable_inj; 1: smt().
  rewrite summable_mu1.
rewrite sum_pair.
  apply LHS_summable.
rewrite sum_swap.
  apply LHS_summable.
apply eq_sum => v /=.
rewrite - sumZ.
apply eq_sum => z /=.
case (bad_event z v).
* move => bad_ev.
  rewrite dA_output_bad; 1: by assumption.
  smt().
* move => neg_bad_ev.
  rewrite dA_output_good; 1: by assumption.
  smt().
qed.

lemma dA_output_something_summable_inner :
  forall v,
    summable (fun (z : varMatrix) =>
      if bad_event z v then mu1 (g v) z else mu1 f z / M).
proof.
move => v.
apply (summable_le_pos _ (fun z => mu1 (g v) z + mu1 f z / M)).
* (* upper sequence is summable *)
  apply summableD; 1: by apply summable_mu1.
  have rewrite_under_binding : (fun x => mu1 f x / M) = (fun x => (1%r / M) * mu1 f x).
    apply fun_ext => /#.
  rewrite rewrite_under_binding.
  apply summableZ.
  by apply summable_mu1.
* (* upper sequence is correct *)
  move => z /=.
  (* -- ANTI-PATTERN? -- *)
  (* hints for smt...? *)
  have mu_gv_ge0 : mu1 (g v) z >= 0%r by apply ge0_mu.
  have mu_fz_ge0 : mu1 f z >= 0%r by apply ge0_mu.
  have m_pos : M > 0%r by apply M_positive.
  smt().
qed.

lemma dA_output_something_summable :
  summable (fun (v : V) =>
    mu1 h v *
    sum (fun (z : varMatrix) =>
      if bad_event z v then mu1 (g v) z else mu1 f z / M)).
proof.
(* Bringing this into context so smt works *)
have m_pos : M > 0%r by apply M_positive.

apply (summableM_bound (1%r + 1%r / M) _ _).
* smt().
* (* left side summable *)
  apply summable_mu1.
* (* right side bounded *)
  move => v /=.
  have abs_removable :
    sum (fun (z : varMatrix) =>
     if bad_event z v then mu1 (g v) z else mu1 f z / M) >= 0%r.
    apply ge0_sum => /= z.
    case (bad_event z v).
    * move => _. apply ge0_mu.
    * move => _.
      have remove_denom : forall (a b : real), a > 0%r => b >= 0%r => b / a >= 0%r.
        smt().
      apply remove_denom.
        apply M_positive.
      apply ge0_mu.
  rewrite /"`|_|".
  rewrite abs_removable => /=.
  have bound_by_sum :
    sum (fun (z : varMatrix) => if bad_event z v then mu1 (g v) z else mu1 f z / M) <=
    sum (fun (z : varMatrix) => mu1 (g v) z + mu1 f z / M).
    apply ler_sum_pos.
    * move => z /=.
      split.
      * case (bad_event z v).
        * move => unused. apply ge0_mu.
        * move => unused.
          have remove_denom : forall (a b : real), a > 0%r => b >= 0%r => b / a >= 0%r.
            smt().
          apply remove_denom.
          apply M_positive.
          by apply ge0_mu.
      * move => _.
        case (bad_event z v).
        * move => _.
          have mu_pos : mu1 f z >= 0%r by apply ge0_mu.
          smt().
        * move => _.
          have muf_pos : mu1 f z >= 0%r by apply ge0_mu.
          have mugv_pos : mu1 (g v) z >= 0%r by apply ge0_mu.
          smt().
    * apply summableD.
      apply summable_mu1.
      have rewrite_under_binding :
          (fun (x : varMatrix) => mu1 f x / M) = (fun (x : varMatrix) => (1%r / M) * mu1 f x).
        by apply fun_ext => /#.
      rewrite rewrite_under_binding.
      apply summableZ.
      by apply summable_mu1.
  have sum_bounded : (sum (fun (z : varMatrix) => mu1 (g v) z + mu1 f z / M) <= (1%r + 1%r / M)).
    rewrite sumD.
    * apply summable_mu1.
    * have rewrite_under_binding :
        (fun (x : varMatrix) => mu1 f x / M) = (fun (x : varMatrix) => (1%r / M) * mu1 f x).
        apply fun_ext => /#.
      rewrite rewrite_under_binding.
      apply summableZ.
      apply summable_mu1.
    * have sum_gv_leq1 : (sum (fun (x : varMatrix) => mu1 (g v) x) <= 1%r).
        rewrite -weightE.
        apply le1_mu.
      have sum_fv_leq1_invM : sum (fun (x : varMatrix) => mu1 f x / M) <= 1%r / M.
        have rewrite_under_binding :
          (fun (x : varMatrix) => mu1 f x / M) = (fun (x : varMatrix) => (1%r / M) * mu1 f x).
          apply fun_ext => /#.
        rewrite rewrite_under_binding.
        rewrite sumZ.
        have mufx_leq_1 : (sum (fun (x : varMatrix) => mu1 f x) <= 1%r).
          rewrite - weightE.
          by apply le1_mu.
        smt().
      smt().
  smt().
qed.

lemma dA_output_something_lowerbound :
    forall eps, bad_event_unlikely eps =>
    mu dA (fun x => x <> None) >= (1%r - eps) / M.
proof.
  have m_pos : M > 0%r by apply M_positive.
  move => eps bad_event_eps.
  rewrite (dA_output_something eps).
    assumption.
  have first_hop :
    ((sum (fun (v : V) =>
      mu1 h v *
      sum (fun (z : varMatrix) =>
        if bad_event z v then mu1 (g v) z else mu1 f z / M))) >=
    (sum (fun (v : V) =>
      mu1 h v *
      sum (fun (z : varMatrix) =>
        if bad_event z v then 0%r else mu1 f z / M)))).
    apply ler_sum_pos.
    simplify.
    move => v.
    split.
    * have product_of_positives :
        forall (a b : real), a >= 0%r => b >= 0%r => a * b >= 0%r.
        smt().
      apply product_of_positives.
      apply ge0_mu.
      apply ge0_sum.
      move => z.
      simplify.
      case (bad_event z v).
      * move => bad_ev.
        smt().
      * have mu1_fz_ge0 : mu1 f z >= 0%r by apply ge0_mu.
        smt().
    move => unused.
    clear unused.
    have left_cancel :
      forall (a b c : real), a >= 0%r => b <= c => a * b <= a * c.
      smt().
    apply left_cancel.
      apply ge0_mu.
    clear left_cancel.
    apply ler_sum_pos.
    move => z.
    have mu1_fz_ge0 : mu1 f z >= 0%r by apply ge0_mu.
    simplify.
    case (bad_event z v).
    * move => bad_ev.
      split.
      * smt().
      * move => unused.
        apply ge0_mu.
    * move => bad_ev.
      split.
      * smt().
      * smt().
    apply dA_output_something_summable_inner.
    apply dA_output_something_summable.
  have second_hop :
    (sum (fun (v : V) =>
      mu1 h v *
      sum (fun (z : varMatrix) =>
        if bad_event z v then 0%r else mu1 f z / M)) >=
    (1%r - eps) / M).
    have inner_bound : forall v,
      sum (fun (z : varMatrix) => if bad_event z v then 0%r else mu1 f z / M) >= (1%r - eps) / M.
      move => v.
      have if_good_event :
        sum (fun z => if bad_event z v then 0%r else mu1 f z / M) =
        sum (fun z => if ! (bad_event z v) then mu1 f z / M else 0%r).
        apply eq_sum.
        move => z.
        simplify.
        smt().
      rewrite if_good_event.
      have good_event_likely :
        mu f (fun z => ! bad_event z v) >= 1%r - eps.
        have mu_good_ev :
          mu f predT = mu f (predI predT (fun z => bad_event z v))
            + mu f (predI predT (predC (fun z => bad_event z v))) by apply mu_split.
        have weight_f : weight f = 1%r by apply f_ll.
        have mu_bad_ev :
          mu f (predI predT (fun z => bad_event z v)) = mu f (fun z => bad_event z v).
          rewrite predTI.
          auto.
          rewrite /bad_event_unlikely in bad_event_eps.
        have bad_event_simpl :
          mu f (predI predT (predC (transpose bad_event v))) =
          mu f (fun (z : varMatrix) => ! bad_event z v).
          rewrite /predC.
          rewrite predTI.
          auto.
        rewrite - weight_f.
        rewrite mu_good_ev.
        rewrite - bad_event_simpl.
        rewrite mu_bad_ev.
        have arith :
          forall (a b c : real), a <= c => a + b - c <= b.
          smt().
        apply arith.
        apply bad_event_eps.
      have factor_out_M_from_if :
        sum (fun (z : varMatrix) => if ! bad_event z v then mu1 f z / M else 0%r) =
        sum (fun (z : varMatrix) => (if ! bad_event z v then mu1 f z else 0%r) / M).
        apply eq_sum.
        smt().
      have factor_out_M :
        sum (fun (z : varMatrix) => if ! bad_event z v then mu1 f z / M else 0%r) =
        (sum (fun (z : varMatrix) => if ! bad_event z v then mu1 f z else 0%r)) / M.
        rewrite factor_out_M_from_if.
        have lhs_invm :
          sum (fun (z : varMatrix) => (if ! bad_event z v then mu1 f z else 0%r) / M) =
          sum (fun (z : varMatrix) => (inv M) * (if ! bad_event z v then mu1 f z else 0%r)).
        apply eq_sum. smt().
        rewrite lhs_invm. clear lhs_invm.
        rewrite sumZ.
        smt().
      rewrite factor_out_M.
      clear factor_out_M_from_if.
      clear factor_out_M.
      have no_M_subcase :
        1%r - eps <= sum (fun z => if (! bad_event z v) then mu1 f z else 0%r).
        rewrite muE in good_event_likely.
        smt().
      smt().
    have bound_const_factor :
      sum (fun (v : V) =>
         mu1 h v *
         sum (fun (z : varMatrix) => if bad_event z v then 0%r else mu1 f z / M)) >=
      sum (fun (v : V) =>
        mu1 h v * (1%r - eps) / M).
      apply ler_sum.
      move => v /=.
      have arith :
        forall (a b c d : real), a >= 0%r => b / d <= c => a * b / d <= a * c.
        smt().
      apply arith.
        apply ge0_mu.
      clear arith.
      apply inner_bound.
      have under_binding :
        (fun v => mu1 h v * (1%r - eps) / M) = (fun v => ((1%r - eps) / M) * (mu1 h v)).
        apply fun_ext.
        smt().
      rewrite under_binding.
      clear under_binding.
      apply summableZ.
      apply summable_mu1.
    * apply (summable_le_pos _
        (fun v => mu1 h v * sum (fun (z : varMatrix) =>
          if bad_event z v then mu1 (g v) z else mu1 f z / M))
        ).
      * apply dA_output_something_summable.
        move => v /=.
        split.
        have prod_geq0 : forall (a b : real), a >= 0%r => b >= 0%r => a * b >= 0%r.
          smt().
        apply prod_geq0.
        * rewrite ge0_mu.
        * apply ge0_sum.
          move => z /=.
          case (bad_event z v).
          * auto.
          * have mu1_fz_geq0 : mu1 f z >= 0%r by apply ge0_mu.
            smt().
      * move => unused. clear unused.
        have ineq : forall (a b c : real), a >= 0%r => b <= c => a * b <= a * c.
          smt().
        apply ineq.
          apply ge0_mu.
        clear ineq.
        apply ler_sum.
        move => z /=.
        have mu1_gv_geq0 : mu1 (g v) z >= 0%r by apply ge0_mu.
        smt().
    * apply (summable_le_pos _ (
        fun (z : varMatrix) => if bad_event z v then mu1 (g v) z else mu1 f z / M
      )).
      * apply dA_output_something_summable_inner.
      * move => z /=.
        split.
        * have mu1_fz_pos : mu1 f z >= 0%r by apply ge0_mu.
          smt().
        * move => unused; clear unused.
          have mu1_gv_pos : mu1 (g v) z >= 0%r by apply ge0_mu.
          smt().
      apply dA_output_something_summable_inner.
    have sum_hv :
      sum (fun (v : V) => mu1 h v * (1%r - eps) / M) = (1%r - eps) / M.
      have under_binding : sum (fun (v : V) => mu1 h v * (1%r - eps) / M) =
        sum (fun (v : V) => ((1%r - eps) / M) * mu1 h v).
        apply eq_sum.
        smt().
      rewrite under_binding.
      clear under_binding.
      rewrite sumZ.
      have hll : sum (fun (x : V) => mu1 h x) = 1%r.
        have w : sum (fun (x : V) => mu1 h x) = sum (mu1 h).
          apply eq_sum.
          move => v /=.
          auto.
        rewrite w.
        rewrite - weightE.
        apply h_ll.
      smt().
    rewrite - sum_hv.
    apply bound_const_factor.
  have le_trans :
    forall (a b c : real), a <= b => b <= c => a <= c.
  smt().
  apply (le_trans _ (sum (fun (v : V) =>
      mu1 h v *
      sum (fun (z : varMatrix) =>
        if bad_event z v then 0%r else mu1 f z / M))) _).
  assumption.
  assumption.
qed.

lemma dA_output_something_upperbound :
  forall eps, bad_event_unlikely eps =>
  mu dA (fun x => x <> None) <= 1%r / M.
proof.
  move => eps bad_eps.
  rewrite (dA_output_something eps).
    assumption.
  have first_hop :
    sum (fun v => mu1 h v *
      sum (fun z => if bad_event z v then mu1 (g v) z else mu1 f z / M)) <=
    sum (fun v => mu1 h v *
      sum (fun z => mu1 f z / M)).
    * apply ler_sum.
      * (* ler : le *)
        move => v /=.
        have inner_ler_sum :
          sum (fun (z : varMatrix) => if bad_event z v then mu1 (g v) z else mu1 f z / M) <=
            sum (fun (z : varMatrix) => mu1 f z / M).
        * apply ler_sum.
          * (* ler : le *)
            move => z /=.
            case (bad_event z v).
            * rewrite /bad_event.
              move => bad_ev.
              have arith :
                forall (a b c : real),
                  a > 0%r => b >= 0%r => c >= 0%r => a * b < c => b <= c / a.
                smt().
              apply arith.
              * apply M_positive.
              * apply ge0_mu.
              * apply ge0_mu.
              * apply bad_ev.
            * auto.
          * (* ler_sum : summable *)
            apply dA_output_something_summable_inner.
          * (* ler_sum : summable *)
            have factor_invM :
              (fun (z : varMatrix) => mu1 f z / M) = (fun (z : varMatrix) => (inv M) * (mu1 f z)).
            * apply fun_ext.
              smt().
            rewrite factor_invM. clear factor_invM.
            apply summableZ.
            apply summable_mu1.
        have mu1_hv_ge0 : mu1 h v >= 0%r by apply ge0_mu.
        smt().
      * (* ler_sum : summable *)
        apply dA_output_something_summable.
      * (* ler_sum : summable *)
        move.
        have inner_sum_simpl :
          (fun (v : V) => mu1 h v * sum (fun (z : varMatrix) => mu1 f z / M)) =
          (fun (v : V) => (inv M) * (mu1 h v)).
        * apply fun_ext.
          move => v /=.
          have sum_eval :
            sum (fun (z : varMatrix) => mu1 f z / M) = 1%r / M.
          * have sum_factor_Minv :
              sum (fun (z : varMatrix) => mu1 f z / M) =
              sum (fun (z : varMatrix) => (inv M) * (mu1 f z)).
            * apply eq_sum => //.
            rewrite sum_factor_Minv. clear sum_factor_Minv.
            rewrite sumZ.
            rewrite - weightE.
            rewrite f_ll.
            auto.
          rewrite sum_eval.
          auto.
        rewrite inner_sum_simpl.
        apply summableZ.
        apply summable_mu1.
  have second_hop :
    sum (fun v => mu1 h v *
      sum (fun z => mu1 f z / M)) = 1%r / M.
  * clear first_hop.
    have inner_eq :
      sum (fun (v : V) => mu1 h v * sum (fun (z : varMatrix) => mu1 f z / M)) =
      sum (fun (v : V) => (inv M) * (mu1 h v)).
    * apply eq_sum.
      move => v /=.
      have sum_factor_Minv :
        sum (fun (z : varMatrix) => mu1 f z / M) =
        sum (fun (z : varMatrix) => (inv M) * (mu1 f z)).
      * apply eq_sum.
      move => z //.
      rewrite sum_factor_Minv. clear sum_factor_Minv.
      rewrite sumZ.
      have using_ll :
        sum (fun (x : varMatrix) => mu1 f x) = 1%r.
      * rewrite - weightE.
        rewrite f_ll.
        auto.
      rewrite using_ll.
      auto.
    rewrite inner_eq.
    rewrite sumZ.
    rewrite - weightE.
    rewrite h_ll.
    auto.
  rewrite - second_hop.
  apply first_hop.
qed.

(* lemma needs the probability of dA outputting _nothing_ *)

lemma dA_output_nothing :
  mu dA (fun x => x = None) = 1%r - mu dA (fun x => x <> None).
proof.
  have mu_not_inst :
     mu dA (predC (fun x => x <> None)) = weight dA - mu dA (fun x => x <> None) by apply mu_not.
  rewrite - dA_ll.
  have predC_under_fn : (fun (x : (varMatrix * V) option) => x = None) = (predC (fun x => x <> None)).
    apply fun_ext.
    smt().
  rewrite predC_under_fn.
  apply mu_not_inst.
qed.

lemma dA_output_nothing_lower :
  forall eps,
  bad_event_unlikely eps =>
    mu dA (fun x => x = None) >= 1%r - 1%r / M.
proof.
  move => eps bad_event_eps.
  rewrite dA_output_nothing.
  have dA_output_upper :
    mu dA (fun (x : (varMatrix * V) option) => x <> None) <= 1%r / M.
  * apply (dA_output_something_upperbound eps).
    assumption.
  smt().
qed.

lemma dA_output_nothing_upper :
  forall eps,
  bad_event_unlikely eps =>
    mu dA (fun x => x = None) <= 1%r - (1%r - eps) / M.
proof.
  move => eps bad_event_eps.
  rewrite dA_output_nothing.
  have dA_output_lower_inst :
    (1%r - eps) / M <= mu dA (fun (x : (varMatrix * V) option) => x <> None).
  * apply (dA_output_something_lowerbound eps).
    assumption.
  smt().
qed.

(* -- Now do the same analysis with dF -- *)

op dF = dlet h (fun v =>
  dlet f (fun z =>
    dlet (dbiased (1%r / M))
      (fun good => dunit (if good then Some (z, v) else None))
  )
).

lemma dF_ll :
  is_lossless dF.
proof.
  rewrite /dF.
  apply dlet_ll.
  apply h_ll.
  move => v v_supp /=.
  apply dlet_ll.
  apply f_ll.
  move => z z_supp /=.
  apply dlet_ll.
  apply dbiased_ll.
  move => good good_supp /=.
  apply dunit_ll.
qed.

axiom m_geq1 : M >= 1%r.

lemma invM_clamped :
  clamp (inv M) = inv M.
proof.
  have m_geq1_inst : M >= 1%r by apply m_geq1.
  smt().
qed.

lemma dF_some_1E :
  forall z v, mu1 dF (Some (z, v)) = (mu1 h v) * (mu1 f z) / M.
proof.
  move => z v.
  rewrite /dF.
  rewrite dlet1E => /=.
  rewrite (sumE_fin _ [v]).
  * auto.
  * (* zero outside [v] *)
    move => x /=.
    case (x = v).
    auto.
    move => xv_neq /=.
    rewrite dlet1E => /=.
    have left_cancel : forall a b, b = 0%r => a * b = 0%r by smt().
    apply left_cancel.
    apply sum0_eq.
    move => z_ /=.
    apply left_cancel.
    rewrite dlet1E => /=.
    rewrite sum_over_bool => /=.
    rewrite dunit1E.
    rewrite dunit1E.
    smt().
  rewrite /big.
  simplify.
  rewrite foldr_map => /=.
  rewrite /predT => /=.
  rewrite dlet1E => /=.
  rewrite (sumE_fin _ [z]).
  * auto.
  * (* zero outside [z] *)
    move => x /=.
    case (x = z).
    auto.
    move => xz_neq /=.
    have left_cancel : forall a b, b = 0%r => a * b = 0%r by smt().
    apply left_cancel.
    rewrite dlet1E => /=.
    rewrite sum_over_bool => /=.
    rewrite dunit1E.
    rewrite dunit1E.
    smt().
  rewrite /big => /=.
  rewrite foldr_map => /=.
  rewrite /predT => /=.
  rewrite dlet1E => /=.
  rewrite sum_over_bool => /=.
  rewrite dbiased1E.
  rewrite dbiased1E.
  simplify.
  rewrite invM_clamped.
  rewrite dunit1E.
  rewrite dunit1E.
  auto.
qed.

lemma dF_none_1E :
  mu1 dF None = 1%r - 1%r / M.
proof.
  rewrite /dF.
  rewrite dlet1E => /=.
  have fun_simpl :
    (fun v => mu1 h v *
       mu1 (dlet f
         (fun z => dlet (dbiased (inv M))
            (fun good =>
               dunit (if good then Some (z, v) else None)))) None) =
    (fun v => (1%r - inv M) * (mu1 h v)).
  * apply fun_ext.
    move => v /=.
    rewrite dlet1E => /=.
    have fun_simpl2 :
      (fun z => mu1 f z * mu1 (dlet (dbiased (inv M))
         (fun good => dunit (if good then Some (z, v) else None))) None) =
      (fun z => (1%r - inv M) * (mu1 f z)).
    * apply fun_ext.
      move => z /=.
      rewrite dlet1E => /=.
      rewrite sum_over_bool => /=.
      rewrite dbiased1E.
      rewrite dbiased1E.
      rewrite dunit1E.
      rewrite dunit1E.
      rewrite invM_clamped.
      smt().
    rewrite fun_simpl2.
    rewrite sumZ.
    (* summing over all z gives 1 *)
    rewrite - weightE.
    rewrite f_ll.
    smt().
  rewrite fun_simpl.
  rewrite sumZ.
  (* summing over all v gives 1 *)
  rewrite - weightE.
  rewrite h_ll.
  auto.
qed.

lemma lem4_7_firsthalf :
  forall eps,
    bad_event_unlikely eps =>
    (sdist dA dF <= eps / M).
proof.
  move => eps mu_bad_event.
  rewrite sdist_tvd.
  rewrite dF_ll.
  rewrite dA_ll.
  simplify.
  rewrite StdOrder.RealOrder.normr0 => /=.
  rewrite sumD1_None.
  * apply summable_sdist.
  simplify.
  have summable_sdist_tvd_some :
    summable (fun (y : varMatrix * V) => `|mu1 dA (Some y) - mu1 dF (Some y)|).
  * apply (summable_inj Some (fun sy => `|mu1 dA sy - mu1 dF sy|)).
    auto.
    apply summable_sdist.
  have each_term_bound :
    forall (a b : real), a <= eps / M => b <= eps / M => (a + b) / 2%r <= eps / M.
    smt().
  apply each_term_bound.
  * clear each_term_bound.
    rewrite sum_pair.
    * apply summable_sdist_tvd_some.
    rewrite sum_swap.
    * assumption.
    simplify.
    have inner_sum_simpl :
      (fun v => (sum (fun z => `|mu1 dA (Some (z, v)) - mu1 dF (Some (z, v))|))) =
      fun v => (sum (fun z =>
        if bad_event z v then `| mu1 h v * mu1 (g v) z - mu1 h v * mu1 f z / M | else 0%r)).
    * apply fun_ext.
      move => v /=.
      apply eq_sum => z /=.
      case (bad_event z v).
      * move => bad_ev.
        rewrite dA_output_bad.
          assumption.
        rewrite dF_some_1E.
        smt().
      * move => good_ev.
        rewrite dA_output_good.
          assumption.
        rewrite dF_some_1E.
        smt().
    rewrite inner_sum_simpl.
    clear inner_sum_simpl.
    have leq_trans :
      forall (a b c : real), a <= b => b <= c => a <= c.
      smt().
    apply (leq_trans _ (
      sum (fun v =>
        sum (fun z =>
          if bad_event z v then mu1 h v * mu1 f z / M else 0%r))) _).
    * apply ler_sum.
      * move => v /=.
        apply ler_sum.
        * move => z /=.
          case (bad_event z v).
          * move => bad_ev.
            rewrite /bad_event in bad_ev.
            (* hints for smt to solve inequalities *)
            (* I have no idea how to solve inequalities without smt *)
            have mu_gv_ge0 : mu1 (g v) z >= 0%r by apply ge0_mu.
            have mu_hv_ge0 : mu1 h v >= 0%r by apply ge0_mu.
            have mu_fz_ge0 : mu1 f z >= 0%r by apply ge0_mu.
            have m_geq1_inst : M >= 1%r by apply m_geq1.

            have eqr_normN_inst : forall (x : real), x <= 0%r => `|x| = -x.
              move => x eq_leq0.
              apply StdOrder.RealOrder.eqr_normN.
              assumption.
            rewrite eqr_normN_inst.
              smt().
            smt().
          * auto.
        * (* ler_sum summable *)
          apply (summable_le_pos _ (fun z => mu1 (g v) z + mu1 f z)).
          * (* upper is summable *)
            apply summableD; apply summable_mu1.
          * (* upper is correct *)
            move => z /=.
            case (bad_event z v).
            * move => bad_ev.
              split.
              * smt().
              * move => unused.
                apply (leq_trans _ (mu1 h v * mu1 (g v) z + mu1 h v * mu1 f z / M) _).
                * (* triangle ineq? *)
                  apply (leq_trans _ (`|mu1 h v * mu1 (g v) z| + `|mu1 h v * mu1 f z / M|) _ ).
                  apply StdOrder.RealOrder.ler_norm_sub.
                  have sum_of_norm_geq0 :
                    forall (a b : real), a >= 0%r => b >= 0%r => `|a| + `|b| <= a + b by smt().
                  apply sum_of_norm_geq0.
                  have prod_of_geq0 : forall a b, a >= 0%r => b >= 0%r => a * b >= 0%r by smt().
                  apply prod_of_geq0; apply ge0_mu.
                  have prod_of_geq0_invM :
                    forall a b m, a >= 0%r => b >= 0%r => m >= 1%r => a * b / m >= 0%r by smt().
                  apply prod_of_geq0_invM.
                    rewrite ge0_mu.
                    rewrite ge0_mu.
                    apply m_geq1.
                * have ineq_fact :
                    forall (f1 f2 t1 t2 : real),
                      (f1 <= 1%r) => (f2 >= 1%r) => (t1 >= 0%r) => (t2 >= 0%r) =>
                      (f1 * t1 + f1 * t2 / f2 <= t1 + t2) by smt().
                  apply ineq_fact.
                  apply le1_mu.
                  apply m_geq1.
                  apply ge0_mu.
                  apply ge0_mu.
            * move => neg_bad_ev.
              split. auto. move => unused.
              have sum_of_geq0 : forall (a b : real), a >= 0%r => b >= 0%r => a + b >= 0%r by smt().
              apply sum_of_geq0; apply ge0_mu.
        * (* ler_sum summable *)
          apply (summable_le_pos _ (fun z => (mu1 h v / M) * mu1 f z)).
          * (* upper summable *)
            apply summableZ.
            apply summable_mu1.
          * (* upper correct *)
            move => z /=.
            case (bad_event z v) => unused.
            * split.
              * have ineq_fact :
                  forall a b c,
                    a >= 0%r => b >= 0%r => c >= 1%r => a * b / c >= 0%r by smt().
                apply ineq_fact.
                apply ge0_mu.
                apply ge0_mu.
                apply m_geq1.
              * auto.
            * split.
              * auto.
                move => unused2.
                have ineq_fact :
                  forall a b c,
                    a >= 0%r => b >= 0%r => c >= 1%r => a * b / c >= 0%r by smt().
                apply ineq_fact.
                apply ge0_mu.
                apply ge0_mu.
                apply m_geq1.
      * (* ler_sum summable *)
        apply (summable_le_pos _ (fun v => 2%r * mu1 h v)).
        * (* summable_le_pos - upper summable *)
          apply summableZ.
          apply summable_mu1.
        * (* summable_le_pos - upper correct *)
          move => v /=.
          split.
          * (* upper >= 0 *)
            simplify.
            apply ge0_sum => z /=.
            smt().
          * (* upper bounded *)
            move => unused; clear unused.
            (* this will be kinda unfun. *)
            apply (leq_trans  _ (sum (fun z => mu1 h v * `|mu1 (g v) z - mu1 f z / M|)) _).
            * (* first hop *)
              apply ler_sum.
              * (* le *)
                move => z /=.
                case (bad_event z v).
                * move => unused.
                  have group_terms : forall (a b c d : real), d >= 1%r =>
                    a * b - a * c / d = a * (b - c / d) by smt().
                  rewrite group_terms.
                    apply m_geq1.
                  have mu1_hv_ge0 : mu1 h v >= 0%r by apply ge0_mu.
                  rewrite normrZ.
                    apply ge0_mu.
                  auto.
                * move => unused.
                  have prod_ge0 : forall a b, a >= 0%r => b >= 0%r => a * b >= 0%r by smt().
                  apply prod_ge0.
                  apply ge0_mu.
                  smt().
              * (* summable 1 *)
                apply (summable_le_pos _ (fun z => mu1 (g v) z + inv M * mu1 f z)).
                * apply summableD.
                  * apply summable_mu1.
                  * apply/summableZ/summable_mu1.
                * move => z /=.
                  split.
                  * smt().
                  * move => unused. (*
                    have gvz_ge0 : mu1 (g v) z >= 0%r by rewrite - massE; apply ge0_mass.
                    have hv_ge0 : mu1 h v >= 0%r by rewrite - massE; apply ge0_mass.
                    have fz_ge0 : mu1 f z >= 0%r by rewrite - massE; apply ge0_mass.
                    have m_geq1_inst : M >= 1%r by apply m_geq1. *)
                    case (bad_event z v).
                    * clear unused; move => unused; clear unused.
                      have group_terms : forall (a b c d : real), d >= 1%r =>
                        a * b - a * c / d = a * (b - c / d) by smt().
                      rewrite group_terms.
                        apply m_geq1.
                      (* have mu1_hv_ge0 : mu1 h v >= 0%r by rewrite - massE; apply ge0_mass. *)
                      rewrite normrZ.
                        apply ge0_mu.
                      (* have mu1_hv_le1 : mu1 h v <= 1%r by rewrite - massE; apply le1_mass. *)
                      have cancel_factor : forall (a b c : real),
                        0%r <= a <= 1%r => b >= 0%r => c >= 0%r =>
                        b <= c => a * b <= c by smt().
                      apply cancel_factor.
                        split.
                        apply ge0_mu.
                        move => _. apply le1_mu.
                        smt().
                        have gvz_ge0 : mu1 (g v) z >= 0%r by apply ge0_mu.
                        have fz_ge0 : mu1 f z >= 0%r by apply ge0_mu.
                        have m_ge1_inst : M >= 1%r by apply m_geq1.
                        smt(). 
                      apply (leq_trans _ (`|mu1 (g v) z| + `|mu1 f z / M|)).
                      apply StdOrder.RealOrder.ler_norm_sub.
                      rewrite ger0_norm.
                        apply ge0_mu.
                      rewrite ger0_norm.
                        have fz_ge0 : mu1 f z >= 0%r by apply ge0_mu.
                        have m_geq1_inst : M >= 1%r by apply m_geq1.
                        smt().
                      auto.
                    * clear unused; move => unused; clear unused.
                      have ineq_fact : forall (a b c : real),
                        a >= 0%r => b >= 0%r => c >= 1%r =>
                        a + b / c >= 0%r by smt().
                      apply ineq_fact.
                        apply ge0_mu.
                        apply ge0_mu.
                        apply m_geq1.
              * (* summable 2 *)
                apply summableZ.
                apply (summable_le_pos _ (fun z => mu1 (g v) z + inv M * mu1 f z)).
                * apply summableD.
                  * apply summable_mu1.
                  * apply/summableZ/summable_mu1.
                * move => z /=.
                  split.
                  * smt().
                  * move => unused. clear unused.
                    apply (leq_trans _ (`|mu1 (g v) z| + `|mu1 f z / M|)).
                    apply StdOrder.RealOrder.ler_norm_sub.
                    rewrite StdOrder.RealOrder.ger0_norm.
                      apply ge0_mu.
                    rewrite StdOrder.RealOrder.ger0_norm.
                      have fz_ge0 : mu1 f z >= 0%r by apply ge0_mu.
                      have m_ge0_inst : M >= 1%r by apply m_geq1.
                      smt().
                    auto.
            * (* second hop *)
              rewrite sumZ.
              have cancel_const :
                forall (a b c : real), a >= 0%r => b <= c => a * b <= c * a by smt().
              apply cancel_const.
              apply ge0_mu.
              apply (leq_trans _ (sum (fun z => mu1 (g v) z + mu1 f z / M)) _).
              * (* triangle *)
                apply ler_sum.
                * (* le *)
                  move => z /=.

                  apply (leq_trans _ (`|mu1 (g v) z| + `|mu1 f z / M|)).
                  apply StdOrder.RealOrder.ler_norm_sub.
                  rewrite StdOrder.RealOrder.ger0_norm.
                    apply ge0_mu.
                  rewrite StdOrder.RealOrder.ger0_norm.
                    have fz_ge0 : mu1 f z >= 0%r by
                    apply ge0_mu.
                    have m_ge0_inst : M >= 1%r by apply m_geq1.
                    smt().
                  auto.
                * (* summable 1 *)
                  apply (summable_le_pos _ (fun z => `|mu1 (g v) z| + `|mu1 f z / M|)).
                  * (* summable_le_pos summable *)
                    apply summableD.
                    * have norm_extraneous :
                        (fun z => `|mu1 (g v) z|) = (fun z => mu1 (g v) z).
                      * apply fun_ext => z /=.
                        apply StdOrder.RealOrder.ger0_norm.
                        apply ge0_mu.
                      rewrite norm_extraneous.
                      apply summable_mu1.
                    * have norm_extraneous :
                        (fun z => `|mu1 f z / M|) = (fun z => inv M * mu1 f z).
                      * apply fun_ext => z /=.
                        apply StdOrder.RealOrder.ger0_norm.
                        have fz_ge0 : mu1 f z >= 0%r by apply ge0_mu.
                        have m_geq1_inst : M >= 1%r by apply m_geq1.
                        smt().
                      rewrite norm_extraneous.
                      apply/summableZ/summable_mu1.
                  * (* summable_le_pos correct *)
                    move => z /=.
                    split.
                    * smt().
                    * move => unused; clear unused.
                      apply StdOrder.RealOrder.ler_norm_sub.
                * (* summable 2 *)
                  apply summableD.
                  * apply summable_mu1.
                  * have factorM :
                      (fun (x : varMatrix) => mu1 f x / M) =
                      (fun (x : varMatrix) => inv M * mu1 f x) by apply fun_ext; smt().
                    rewrite factorM.
                    apply/summableZ/summable_mu1.
              * rewrite sumD.
                * apply summable_mu1.
                * have factorM :
                    (fun (x : varMatrix) => mu1 f x / M) =
                    (fun (x : varMatrix) => inv M * mu1 f x) by apply fun_ext; smt().
                  rewrite factorM.
                  apply/summableZ/summable_mu1.
              have factorM :
                (fun (x : varMatrix) => mu1 f x / M) =
                (fun (x : varMatrix) => inv M * mu1 f x) by apply fun_ext; smt().
              rewrite factorM.
              clear factorM.
              rewrite sumZ.
              rewrite - weightE.
              rewrite g_ll.
              rewrite - weightE.
              rewrite f_ll.
              (* hint for smt *)
              have m_ge1_inst : M >= 1%r by apply m_geq1.
              smt().
      * (* ler_sum summable *)
        apply (summable_le_pos _ (fun v => sum (fun z => (mu1 h v / M) * mu1 f z))).
        * (* upper summable *)
          have under_binding :
            (fun (v : V) => sum (fun (z : varMatrix) => mu1 h v / M * mu1 f z)) =
            (fun (v : V) => sum (fun (z : varMatrix) => mu1 f z) * (mu1 h v / M)).
          * apply fun_ext => v /=.
            have more_under_binding :
              (fun (z : varMatrix) => mu1 h v * mu1 f z / M) =
              (fun (z : varMatrix) => (mu1 h v / M) * mu1 f z) by apply fun_ext; smt().
            rewrite more_under_binding.
            rewrite sumZ.
            smt().
          rewrite under_binding; clear under_binding.
          apply summableZ.
          have factor_M : (fun (x : V) => mu1 h x / M) = (fun (x : V) => inv M * mu1 h x)
            by apply fun_ext; smt().
          rewrite factor_M.
          apply summableZ.
          apply summable_mu1.
        * (* upper correct *)
          move => v /=.
          split.
          * (* geq0 *)
            apply ge0_sum.
            move => z /=.
            case (bad_event z v).
            * have ineq_fact : forall a b c, a >= 0%r => b >= 0%r => c >= 1%r => a * b / c >= 0%r.
                smt().
              move => unused.
              apply ineq_fact.
              apply ge0_mu.
              apply ge0_mu.
              apply m_geq1.
            * auto.
          * (* upper bounded *)
            move => unused; clear unused.
            apply ler_sum.
            * (* ler_sum le *)
              move => z /=.
              case (bad_event z v).
              * smt().
              * move => unused.
                have ineq_fact : forall a b c, a >= 0%r => b >= 0%r => c >= 1%r => a * b / c >= 0%r.
                  smt().
                apply ineq_fact.
                apply ge0_mu.
                apply ge0_mu.
                apply m_geq1.
            * (* ler_sum summable *)
              apply (summable_le_pos _ (fun z => (mu1 h v / M) * mu1 f z)).
              * (* upper summable *)
                apply summableZ.
                apply summable_mu1.
              * (* upper correct *)
                move => z /=.
                split.
                * (* ge0 *)
                  case (bad_event z v).
                  * have ineq_fact :
                      forall a b c, a >= 0%r => b >= 0%r => c >= 1%r => a * b / c >= 0%r by smt().
                    move => _.
                    apply ineq_fact.
                    apply ge0_mu.
                    apply ge0_mu.
                    apply m_geq1.
                  * auto.
                * move => _.
                  (* upper bounded *)
                  case (bad_event z v).
                  * auto.
                  * have ineq_fact :
                      forall a b c, a >= 0%r => b >= 0%r => c >= 1%r => a * b / c >= 0%r by smt().
                    move => _.
                    apply ineq_fact.
                    apply ge0_mu.
                    apply ge0_mu.
                    apply m_geq1.
            * (* ler_sum summable *)
              have under_binding :
                (fun (z : varMatrix) => mu1 h v * mu1 f z / M) = fun z => (mu1 h v / M) * mu1 f z.
              * apply fun_ext; smt().
              rewrite under_binding; clear under_binding.
              apply summableZ.
              apply summable_mu1.
    have inner_sum_simpl :
      (fun v => sum
        (fun z => if bad_event z v then mu1 h v * mu1 f z / M else 0%r)) =
      (fun v => (mu1 h v * inv M) * mu f (fun z => bad_event z v)).
    * apply fun_ext.
      move => v /=.
      have under_binding_factor :
        (fun z => if bad_event z v then mu1 h v * mu1 f z / M else 0%r) =
        fun z => (mu1 h v * inv M) * if bad_event z v then mu1 f z else 0%r.
      * apply fun_ext.
        move => z /=.
        case (bad_event z v).
        * smt().
        * smt().
      rewrite under_binding_factor. clear under_binding_factor.
      rewrite sumZ.
      have muE_inst :
        sum (fun (x : varMatrix) => if bad_event x v then mu1 f x else 0%r) =
        mu f (fun z => bad_event z v).
      * rewrite muE.
        simplify.
        by apply eq_sum => z //.
      rewrite muE_inst.
      auto.
    rewrite inner_sum_simpl. clear inner_sum_simpl.
    clear summable_sdist_tvd_some.
    apply (leq_trans _ (
      sum (fun v => (eps * inv M) * mu1 h v)) _).
    * (* hop1 *)
      apply ler_sum.
      * (* ler correct *)
        move => v /=.
        rewrite /bad_event_unlikely in mu_bad_event.
        (* inequality. Hints for smt. *)
        have mu1_hv_ge0 : mu1 h v >= 0%r by apply ge0_mu.
        have m_geq1_inst : M >= 1%r by apply m_geq1.
        have ineq_fact :
          forall (a b c d : real), a >= 0%r => b <= d => c >= 1%r => a * b / c <= d * a / c.
        * smt().
        apply ineq_fact.
          assumption.
          apply mu_bad_event.
          assumption.
      * (* ler summable 1 *)
        apply (summable_le_pos _ (fun v => (eps / M) * mu1 h v)).
        * (* summable_le_pos - upper summable *)
          apply summableZ.
          apply summable_mu1.
        * (* summable_le_pos - bound correct *)
          move => v /=.
          split.
          * (* geq0 *)
            have prod_of_ge0_overM :
              forall (a b m : real),
                a >= 0%r => b >= 0%r => m >= 1%r =>
                a * b / m >= 0%r by smt().
            apply prod_of_ge0_overM.
            * apply ge0_mu.
            * apply ge0_mu.
            * apply m_geq1.
          * (* upperbound *)
            move => unused; clear unused.
            rewrite /bad_event_unlikely in mu_bad_event.
            have ineq_fact :
              forall (m1_hv m_f m e : real),
                m1_hv >= 0%r => m_f <= e => m >= 1%r => m1_hv * m_f / m <= e * m1_hv / m by smt().
            apply ineq_fact.
            apply ge0_mu.
            apply mu_bad_event.
            apply m_geq1.
      * (* ler summable 2 *)
        apply summableZ.
        apply summable_mu1.
    * (* hop2 *)
      rewrite sumZ.
      rewrite - weightE.
      rewrite h_ll.
      auto.
  * rewrite dF_none_1E.
    rewrite /"`|_|".
    case (0%r <= mu1 dA None - (1%r - 1%r / M)).
    * move => unused.
      have dA_output_nothing_upper_inst :
        mu1 dA None <= 1%r - (1%r - eps) / M by apply (dA_output_nothing_upper eps).
      smt().
    * move => unused.
      have dA_output_nothing_lower_inst :
        mu1 dA None >= (1%r - 1%r / M) by apply (dA_output_nothing_lower eps).
      smt().
qed.

lemma lem4_7 :
  forall eps,
    bad_event_unlikely eps =>
    (sdist dA dF <= eps / M) &&
    (mu dA (fun x => x <> None) >= (1%r - eps) / M).
proof.
  move => eps bad_event_eps.
  split.
  * apply lem4_7_firsthalf.
    assumption.
  * move => unused. clear unused.
    apply dA_output_something_lowerbound.
    assumption.
qed.

(*
module A' = {
  proc main() : (varMatrix * V) option = {
     var result; 
     result <$ dA;
     return result;
  }
}.
*)

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
