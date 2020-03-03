From Bignums Require Import BigN.
From Bignums Require Import BigZ.
From Coq Require Import Cyclic31.
From Coq Require Import Cyclic63.
From Coq Require Int31.
From Coq Require Int63.
Require Import Monads.
Require Import Serializable.

Global Instance int31_serializable : Serializable int31.
Proof.
  refine
    {| serialize i := serialize (Int31.phi i);
       deserialize p := do z <- deserialize p; ret (Int31.phi_inv z); |}.
  intros i.
  rewrite deserialize_serialize.
  cbn -[phi phi_inv].
  now rewrite phi_inv_phi.
Defined.

Global Instance int63_serializable : Serializable Int63.int.
Proof.
  refine
    {| serialize i := serialize (Int63.to_Z i);
       deserialize p := do z <- deserialize p; ret (Int63.of_Z z); |}.
  intros i.
  rewrite deserialize_serialize.
  cbn -[Int63.to_Z Int63.of_Z].
  now rewrite of_to_Z.
Defined.

Global Instance zn2z_serializable {A} `{Serializable A} : Serializable (zn2z A).
Proof.
  refine
    {| serialize w1 :=
         serialize
           match w1 with
           | W0 => (0%nat, serialize tt)
           | WW a b => (1%nat, serialize (a, b))
           end;
       deserialize p :=
         do '(tag, p) <- deserialize p;
         match tag with
         | 0%nat => ret W0
         | _ => do '(a, b) <- deserialize p;
                ret (WW a b)
         end |}.
  intros.
  rewrite deserialize_serialize.
  cbn.
  destruct x; auto.
  now rewrite deserialize_serialize.
Defined.
Global Instance word_serializable {A} `{Serializable A} (n : nat) : Serializable (word A n) :=
  (fix f (n : nat) :=
     match n return (Serializable (word A n)) with
     | 0%nat => _ : Serializable A
     | S n => zn2z_serializable
     end) n.

Global Instance BigNw1_serializable : Serializable BigN.w1 := ltac:(apply zn2z_serializable).
Global Instance BigNw2_serializable : Serializable BigN.w2 := ltac:(apply zn2z_serializable).
Global Instance BigNw3_serializable : Serializable BigN.w3 := ltac:(apply zn2z_serializable).
Global Instance BigNw4_serializable : Serializable BigN.w4 := ltac:(apply zn2z_serializable).
Global Instance BigNw5_serializable : Serializable BigN.w5 := ltac:(apply zn2z_serializable).
Global Instance BigNw6_serializable : Serializable BigN.w6 := ltac:(apply zn2z_serializable).
Global Instance BigN_serializable : Serializable bigN.
Proof.
  refine
    {| serialize n :=
         match n with
         | BigN.N0 i => serialize (0, serialize i)
         | BigN.N1 w => serialize (1, serialize w)
         | BigN.N2 w => serialize (2, serialize w)
         | BigN.N3 w => serialize (3, serialize w)
         | BigN.N4 w => serialize (4, serialize w)
         | BigN.N5 w => serialize (5, serialize w)
         | BigN.N6 w => serialize (6, serialize w)
         | BigN.Nn n w => serialize (7, serialize (n, serialize w))
         end%nat;
       deserialize p :=
         do '(tag, p) <- deserialize p;
         match tag with
         | 0 => option_map BigN.N0 (deserialize p)
         | 1 => option_map BigN.N1 (deserialize p)
         | 2 => option_map BigN.N2 (deserialize p)
         | 3 => option_map BigN.N3 (deserialize p)
         | 4 => option_map BigN.N4 (deserialize p)
         | 5 => option_map BigN.N5 (deserialize p)
         | 6 => option_map BigN.N6 (deserialize p)
         | 7 => do '(n, p) <- deserialize p;
                do w <- deserialize p;
                ret (BigN.Nn n w)
         | _ => None
         end%nat |}.
  intros [].
  all: rewrite ?deserialize_serialize; cbn.
  all: rewrite ?deserialize_serialize; easy.
Defined.
Global Instance BigZ_serializable : Serializable bigZ :=
  Derive Serializable BigZ.t__rect<BigZ.Pos, BigZ.Neg>.
