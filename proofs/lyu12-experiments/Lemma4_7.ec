require import AllCore Distr Int List DInterval IntDiv SDist RealSeries.

require VarMatrix.

clone import VarMatrix as IntMat with type ZR.t = int.

(* -- Basic facts that I can't find in the standard library -- *)

lemma mult_cancel_left (x y1 y2 : real):
    (* Really? *)
    y1 = y2 => CoreReal.mul x y1 = CoreReal.mul x y2.
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

(* -- End basic facts -- *)

type V.
op h : V distr.
axiom h_ll: is_lossless h.
op m : int.
op f : varMatrix distr.
axiom f_ll: is_lossless f.
axiom f_shape: forall z, z \in f <=> getDims z = (m, 1).
op M : real.
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
    mu1 dA (Some (z, v)) = mu1 f z / M.
proof.
    move => not_bad.
    rewrite /dA.
    rewrite dlet1E.
    simplify.

    print dlet1E.
    
    have dlet1E_again : 
        mu1 (dlet (g a)
            (fun (z0 : varMatrix) =>
                dlet (dbiased (mu1 f z0 / (M * mu1 (g a) z0)))
                (fun (good : bool) => dunit (if good then Some (z0, a) else None))))
            (Some (z, v)))
        =
        sum (fun z => mu1
    
    .
    auto.

    
    

    smt().


    

lemma dA_inner_none_upperbound_bad:
    forall eps v z,
        mu f (fun z => bad_event z v) < eps =>
        bad_event z v =>
        mu1 dA None
    
op bad_event_eps eps = forall v, mu f (fun z => bad_event z v) < eps.

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
