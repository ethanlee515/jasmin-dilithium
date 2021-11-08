require import AllCore Distr Int List DInterval IntDiv SDist.

require VarMatrix.



clone import VarMatrix as IntMat with type ZR.t = int.

type V.
op h : V distr.
op m : int.
op f : varMatrix distr.
axiom f_shape: forall z, z \in f <=> getDims z = (m, 1).
op M : real.
op g (v : V) : varMatrix distr.
axiom g_shape: forall v z, z \in g v <=> getDims z = (m, 1).

require DBool.

clone import DBool.Biased.

op t = fun good => dunit (if good then Some 0 else None).

print sdist.

op dA = dlet h (fun v =>
    dlet (g v) (fun z =>
        dlet
            (dbiased ((mu1 f z) / M / (mu1 (g v) z)))
            (fun good => dunit (if good then Some (z, v) else None))
    )
).

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
