Require Import Setoid.

Parameter r : relation Prop.

Goal forall P Q : Prop, (r P Q) -> P /\ (P -> Q).
intros P Q H.
Set Debug "rewrite".

setoid_rewrite H.