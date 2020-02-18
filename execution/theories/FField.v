From Coq Require Import ZArith.

Class FField {A : Type} :=
  build_ffield {
    eq_dec (x y : A) : {x = y} + {x <> y};
    zero : A;
    one : A;

    add : A -> A -> A;
    mul : A -> A -> A;

    neg : A -> A;
    inv : A -> A;

    add_comm a b : add a b = add b a;
    add_assoc a b c : add (add a b) c = add a (add b c);

    mul_comm a b : mul a b = mul b a;
    mul_assoc a b c : mul (mul a b) c = mul a (mul b c);

    add_0_l a : add zero a = a;
    mul_0_l a : mul zero a = zero;
    mul_1_l a : mul one a = a;

    neg_inv a : add a (neg a) = a;
    inv_inv a : a <> zero -> mul a (inv a) = a;

    add_mul a b c : mul (add a b) c = add (mul a c) (mul b c);

    (* Everything after this should be derivable from the above *)
    pow : A -> Z -> A;

    pow_0_l e : pow zero e = zero;
    pow_0_r a : pow a 0%Z = one;
  }.

Arguments FField : clear implicits.

Notation "0" := zero : ffield.
Notation "1" := one : ffield.
Infix "+" := add : ffield.
Infix "*" := mul : ffield.
Infix "^" := pow : ffield.

Section FField_aux.
  Context {A : Type}.
  Context `{field: FField A}.

  Local Open Scope ffield.
  Lemma add_0_r a : a + 0 = a.
  Proof. rewrite add_comm; apply add_0_l. Qed.
  Lemma mul_0_r a : a * 0 = 0.
  Proof. rewrite mul_comm; apply mul_0_l. Qed.
  Lemma mul_1_r a : a * 1 = a.
  Proof. rewrite mul_comm; apply mul_1_l. Qed.
  Lemma mul_add a b c : a * (b + c) = a * b + a * c.
  Proof. now rewrite mul_comm, add_mul, 2!(mul_comm a). Qed.
End FField_aux.
