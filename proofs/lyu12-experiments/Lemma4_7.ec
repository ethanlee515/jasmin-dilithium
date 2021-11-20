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

lemma dA_output_good v z:
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


lemma dA_output_bad v z:
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

lemma a_none_upperbound:
    forall eps, bad_event_eps eps => mu1 dA None < eps / M.
proof.
    move => eps bad.
    rewrite /bad_event_eps in bad.
    rewrite /dA.
    rewrite dlet1E.
    simplify.
    print dlet1E.
    have     

    rewrite dlet1E.



    
    smt().
    
op dF = dlet h (fun v =>
  dlet f (fun z =>
        dlet (dbiased (1%r / M))
            (fun good => dunit (if good then Some (z, v) else None))
  )
).

print sum_split.
print sdist.
print sdist_tvd.
print summable_mass.
print le1_mu.
print mu_split.
print mu_disjoint.
print pred0.
print predI.
print predU.
        
print drestrict.
    

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
