Require Import BuiltIn.
Require ZArith.BinInt.
Require ZArith.Znat.

Lemma lemma_z_induction :
  forall P: Z -> Prop, 
    P 0%Z -> (forall i: Z, (i >= 0%Z)%Z -> P i -> P (i+1%Z)%Z) ->
      forall i: Z, (i >= 0%Z)%Z -> P i.
Proof.
intros P HB HS.
pose (Pnat (n : nat) := P (Z.of_nat n)).
assert (forall n : nat, Pnat n).
refine (nat_ind Pnat _ _).
exact HB.
intros n Hp.
assert (Hnat_eq : ((Z.of_nat n)+1%Z)%Z = Z.of_nat (S n)).
exact (eq_sym (Nat2Z.inj_succ n)).
refine (eq_ind (Z.of_nat n + 1)%Z P _ (Z.of_nat (S n)) Hnat_eq).
refine (HS (Z.of_nat n) _ _).
assert (HZ_of_nat_nneg : (Z.of_nat n >= Z.of_nat 0)%Z).
exact (inj_ge n 0 (Nat.le_0_l n)).
exact (eq_ind (Z.of_nat 0) (fun z:Z => (Z.of_nat n >= z)%Z)
  HZ_of_nat_nneg 0%Z Nat2Z.inj_0).
exact Hp.
intros i Hipos.
exact (eq_ind (Z.of_nat (Z.to_nat i)) P (H (Z.to_nat i)) i
  (Z2Nat.id i (proj1 (Z.ge_le_iff i 0) Hipos))).
Qed.

Lemma lemma_z_induction_2 :
  forall P: Z -> Prop, 
    P 0%Z -> (forall i: Z, (0%Z <= i)%Z -> P i -> P (1%Z+i)%Z) ->
      forall i: Z, (0%Z <= i)%Z -> P i.
Proof.
intros P [HB HS] i Hipos.
refine (lemma_z_induction P HB _ i (proj2 (Z.ge_le_iff i 0) Hipos)).
intros i0 Hi0pos HB0.
refine (eq_ind (1+i0)%Z P _ (i0+1)%Z (Z.add_comm 1 i0)).
exact (HS i0 (proj1 (Z.ge_le_iff i0 0) Hi0pos) HB0).
Qed.
