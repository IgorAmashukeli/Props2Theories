Definition el_f (p : Prop) : False -> p := fun (x : False) => 
    match x with
    end.


Ltac intro_true := exact I.
Ltac _intro_true h := assert (h : True) by (exact I).

Ltac elim_false := apply el_f.
Ltac elim_false_ := elim_false; assumption.


Ltac intro_and := split.
Ltac intro_and_ h1 h2 := split; [exact h1 | exact h2].
Ltac _intro_and h1 h2 newH :=
  assert (newH : _ /\ _) by (exact (conj h1 h2)).

Ltac elim_and h h1 h2:= destruct h as [h1 h2].
Ltac elim_and_ h := destruct h as [h1 h2]; assumption.

Ltac elim_or h h1 h2 := destruct h as [h1 | h2].
Ltac elim_or_ h f1 f2:= destruct h as [h1 | h2]; 
[apply f1 in h1; assumption | apply f2 in h2; assumption].
Ltac _elim_or h r newH :=
  match type of h with
  | ?p \/ ?q =>
      assert (newH : (p -> r) -> (q -> r) -> r)
        by (destruct h as [Hp | Hq];
            intros Hp_r Hq_r;
            [apply Hp_r | apply Hq_r]; assumption)
  end.
Ltac _elim_or_app h hpr hqr hr :=
  assert (hr : _)
    by (destruct h as [Hp | Hq];
        [apply hpr | apply hqr]; assumption).


Ltac left_ := left; assumption.
Ltac right_ := right; assumption.
Ltac _left hl r h := let t := type of hl in
assert (h : t \/ r) by (left; exact hl).
Ltac _right hr r h := let t := type of hr in
assert (h_ : r \/ t) by (right; exact hr).

Ltac intro_iff := split.
Ltac intro_iff_ h1 h2 := split; [exact h1 | exact h2].
Ltac _intro_iff h1 h2 h := 
   assert (h : _ <-> _) by (exact (conj h1 h2)).

Ltac _elim_iff h h1 h2 := destruct h as [h1 h2].
Ltac elim_iff_ h := destruct h as [_h1 _h2]; assumption.
Ltac _elim_iff_l h hp hq := pose h as _h2; destruct _h2 as [_hl _hr]; assert (hq : _) by (exact (_hl hp)); clear _hl; clear _hr.
Ltac _elim_iff_r h hq hp := pose h as _h2; destruct _h2 as [_hl _hr]; assert (hp : _) by (exact (_hr hq)); clear _hl; clear _hr.
Ltac elim_iff_l h hp := pose h as _h2; destruct _h2 as [_hl _hr]; assert (_hn : _) by (exact (_hl hp)); clear _hl; clear _hr; assumption.
Ltac elim_iff_r h hq := pose h as _h2; destruct _h2 as [_hl _hr]; assert (_hm : _) by (exact (_hr hq)); clear _hl; clear _hr; assumption.
Ltac elim_iff_l_ h := destruct h as [_hl _hr]; apply _hl; clear _hl; clear _hr.
Ltac elim_iff_r_ h := destruct h as [_hl _hr]; apply _hr; clear _hl; clear _hr.


Ltac intro_neg h := intro h.
Ltac intro_neg_ := assumption.
Ltac _intro_neg hpf hnp := assert (hnp : ~_) by (exact hpf).

Ltac elim_neg h := apply h.
Ltac elim_neg_ h := apply h; assumption.
Ltac _elim_neg_app hp hnp hf := assert (hf : False) by (exact (hnp hp)).
Ltac _elim_neg hpf hnp := assert (hpf : _ -> False) by (exact hnp).
Ltac elim_f_neg hnp := elim_false; elim_neg_ hnp.
Ltac _elim_f_neg hnp v hv := assert (_hfp : False -> v) by (intro _hf; elim_false; assumption); assert (hv : v) by (apply _hfp; elim_neg_ hnp).

Module classical.

Axiom neg_neg_elim : forall {p : Prop}, ((~p) -> False) -> p.

Ltac by_contra h := apply neg_neg_elim; intro h.
Ltac by_contra_ := apply neg_neg_elim; assumption.

Ltac _by_contra hnp hp :=
  let P := match type of hnp with
           | (~?P -> False) => P
           end in
  pose proof (neg_neg_elim hnp) as hp.

End classical.


Ltac exists_ a h := exists a; exact h.
Ltac _exists a h he :=
  let P :=  match type of h with
            | ?P ?a => P
           end in
assert (he : (exists x, P x)) by (exists_ a h).

Ltac exists_elim h a ha := destruct h as [a Ha].

Ltac exists_elim_ h hq := destruct h as [_a _Ha]; specialize (hq _a); apply hq; assumption.

Ltac _exists_elim h Q newH := 
  match type of h with
  | exists x, @?P x =>
      assert (newH : (forall x, P x -> Q) -> Q)
        by (let _w := fresh "_w" in
            let _p := fresh "_p" in
            destruct h as [_w _p];
            let _h_f := fresh "_H" in
            intro _h_f;
            apply _h_f with (x := _w);
            exact _p)
  end; cbv beta in newH.

Ltac _exists_elim_app h Q newH hpq := 
  match type of h with
  | exists x, @?P x =>
      assert (newH : (forall x, P x -> Q) -> Q)
        by (let _w := fresh "_w" in
            let _p := fresh "_p" in
            destruct h as [_w _p];
            let _h_f := fresh "_H" in
            intro _h_f;
            apply _h_f with (x := _w);
            exact _p)
  end; cbv beta in newH; apply newH in hpq.