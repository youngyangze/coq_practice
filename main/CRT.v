Require Import ZArith.
Require Import Znumtheory.
Open Scope Z_scope.

Theorem CRT : forall a b m n : Z,
  m > 0 -> n > 0 -> Z.gcd m n = 1 ->
  exists x : Z, (x mod m = a mod m) /\ (x mod n = b mod n).
Proof.
  intros a b m n Hm Hn Hgcd.
  destruct (Z.ggcd m n) as [u [v d]] eqn:Heq.
  assert (Huv: u*m + v*n = d /\ d = Z.gcd m n) by apply Z.ggcd_spec.
  destruct Huv as [Huv1 Huv2].
  rewrite Hgcd in Huv2.
  assert (H1: u*m + v*n = 1) by (rewrite Huv2; assumption).
  set (x := a*v*n + b*u*m).

  assert (x_eq: x = a + (b - a)*u*m).
  { unfold x.
    rewrite <- H1.
    ring.
  }
  assert (Hxm: x mod m = a mod m).
  { rewrite x_eq.
    apply Z.mod_add; try lia.
    apply Z.divide_factor_l; lia.
  }

  assert (x_eq2: x = b + (a - b)*v*n).
  { unfold x.
    rewrite H1.
    ring.
  }
  assert (Hxn: x mod n = b mod n).
  { rewrite x_eq2.
    apply Z.mod_add; try lia.
    apply Z.divide_factor_l; lia.
  }
  
  exists x.
  split; assumption.
Qed.