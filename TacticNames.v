Definition el_f (p : Prop) : False -> p := fun (x : False) => 
    match x with
    end.

Ltac intro_true := exact I.
Tactic Notation "_intro_true" ident(h) := assert (h : True) by (exact I).

Ltac elim_false := apply el_f.
Ltac elim_false_ := elim_false; assumption.

Ltac intro_and := split.
Tactic Notation "intro_and_" constr(h1) constr(h2) := split; [exact h1 | exact h2].
Tactic Notation "_intro_and" constr(h1) constr(h2) ident(newH) :=
  assert (newH : _ /\ _) by (exact (conj h1 h2)).

Tactic Notation "elim_and" constr(h) ident(h1) ident(h2) := destruct h as [h1 h2].
Tactic Notation "elim_and_" constr(h) := destruct h as [h1 h2]; assumption.

Tactic Notation "elim_or" constr(h) ident(h1) ident(h2) := 
  destruct h as [h1 | h2].

Tactic Notation "elim_or_" constr(h) constr(f1) constr(f2) := 
  destruct h as [h1 | h2]; [apply f1 in h1; assumption | apply f2 in h2; assumption].

Tactic Notation "_elim_or" constr(h) constr(r) ident(newH) :=
  match type of h with

  | ?p \/ ?q =>
      assert (newH : (p -> r) -> (q -> r) -> r)
        by (destruct h as [Hp | Hq];
            intros Hp_r Hq_r;
            [apply Hp_r | apply Hq_r]; assumption)
  end.

Tactic Notation "_elim_or_app" constr(h) constr(hpr) constr(hqr) ident(hr) :=
  assert (hr : _)
    by (destruct h as [Hp | Hq];
        [apply hpr | apply hqr]; assumption).

Ltac left_ := left; assumption.
Ltac right_ := right; assumption.

Tactic Notation "_left" constr(hl) constr(r) ident(h) := 
  let t := type of hl in assert (h : t \/ r) by (left; exact hl).

Tactic Notation "_right" constr(hr) constr(r) ident(h) := 
  let t := type of hr in assert (h : r \/ t) by (right; exact hr).

Ltac intro_iff := split.
Tactic Notation "intro_iff_" constr(h1) constr(h2) := split; [exact h1 | exact h2].
Tactic Notation "_intro_iff" constr(h1) constr(h2) ident(h) := 
   assert (h : _ <-> _) by (exact (conj h1 h2)).

Tactic Notation "_elim_iff" constr(h) ident(h1) ident(h2) := destruct h as [h1 h2].
Tactic Notation "elim_iff_" constr(h) := destruct h as [_h1 _h2]; assumption.

Tactic Notation "_elim_iff_l" constr(h) constr(hp) ident(hq) := 
  pose h as _h2; destruct _h2 as [_hl _hr]; assert (hq : _) by (exact (_hl hp)); clear _hl; clear _hr.

Tactic Notation "_elim_iff_r" constr(h) constr(hq) ident(hp) := 
  pose h as _h2; destruct _h2 as [_hl _hr]; assert (hp : _) by (exact (_hr hq)); clear _hl; clear _hr.

Tactic Notation "_elim_iff_l_" constr(h) constr(hp) ident(hq) := 
  pose h as _h2; destruct _h2 as [_hl _hr]; assert (hq : _) by (exact (_hl hp)); clear _hl; clear _hr; clear hp.

Tactic Notation "_elim_iff_r_" constr(h) constr(hq) ident(hp) := 
  pose h as _h2; destruct _h2 as [_hl _hr]; assert (hp : _) by (exact (_hr hq)); clear _hl; clear _hr; clear hq.

Tactic Notation "elim_iff_l" constr(h) constr(hp) := 
  pose h as _h2; destruct _h2 as [_hl _hr]; assert (_hn : _) by (exact (_hl hp)); clear _hl; clear _hr; assumption.

Tactic Notation "elim_iff_r" constr(h) constr(hq) := 
  pose h as _h2; destruct _h2 as [_hl _hr]; assert (_hm : _) by (exact (_hr hq)); clear _hl; clear _hr; assumption.

Tactic Notation "elim_iff_l_" constr(h) := destruct h as [_hl _hr]; apply _hl; clear _hl; clear _hr.
Tactic Notation "elim_iff_r_" constr(h) := destruct h as [_hl _hr]; apply _hr; clear _hl; clear _hr.

Tactic Notation "intro_neg" ident(h) := intro h.
Ltac intro_neg_ := assumption.
Tactic Notation "_intro_neg" constr(hpf) ident(hnp) := assert (hnp : ~_) by (exact hpf).

Tactic Notation "elim_neg" constr(h) := apply h.
Tactic Notation "elim_neg_" constr(h) := apply h; assumption.
Tactic Notation "_elim_neg_app" constr(hp) constr(hnp) ident(hf) := assert (hf : False) by (exact (hnp hp)).
Tactic Notation "_elim_neg" ident(hpf) constr(hnp) := assert (hpf : _ -> False) by (exact hnp).
Tactic Notation "elim_f_neg" constr(hnp) := elim_false; elim_neg_ hnp.
Tactic Notation "_elim_f_neg" constr(hnp) constr(v) ident(hv) := 
  assert (_hfp : False -> v) by (intro _hf; elim_false; assumption); 
  assert (hv : v) by (apply _hfp; elim_neg_ hnp).

Module classical.
  Axiom neg_neg_elim : forall {p : Prop}, ((~p) -> False) -> p.
  Axiom prop_extens : forall {p q : Prop}, (p <-> q) -> (p = q).

  


  (* Define as Ltac first to preserve the 'classical.' namespace *)
  Ltac by_contra h := apply neg_neg_elim; intro h.
  
  Ltac by_contra_ := apply neg_neg_elim; assumption.

  Ltac _by_contra hnp hp :=
    let P := match type of hnp with
             | (~?P -> False) => P
             end in
    pose proof (neg_neg_elim hnp) as hp.


  Ltac intro_prop_eq h := apply (prop_extens h).

  Ltac intro_prop_eq_ h h_new := 
    let P := match type of h with

          | (?P <-> _) => P
          end 
    in
    let Q := match type of h with
          | (_ <-> ?Q) => Q
          end
    in
    assert (h_new : P = Q) by (exact (prop_extens h)).


End classical.

Tactic Notation "intro_prop_eq" constr(h) := classical.intro_prop_eq h.

Tactic Notation "intro_prop_eq_" constr(h) ident(h_new) := classical.intro_prop_eq_ h h_new.

(* Global Notations that map to the Module's Ltac *)
Tactic Notation "by_contra" ident(h) := classical.by_contra h.

Tactic Notation "by_contra_" := classical.by_contra_.

Tactic Notation "_by_contra" constr(hnp) ident(hp) := 
  classical._by_contra hnp hp.


Tactic Notation "exists_" constr(a) constr(h) := exists a; exact h.
Tactic Notation "_exists" constr(a) constr(h) ident(he) :=
  let P := match type of h with | ?P ?a => P end in
  assert (he : (exists x, P x)) by (exists_ a h).

Tactic Notation "elim_exists" constr(h) ident(a) ident(ha) := destruct h as [a ha].
Tactic Notation "elim_exists_" constr(h) constr(hq) := 
  destruct h as [_a _Ha]; specialize (hq _a); apply hq; assumption.

Tactic Notation "_elim_exists" constr(h) constr(Q) ident(newH) := 
  match type of h with

  | exists x, @?P x =>
      assert (newH : (forall x, P x -> Q) -> Q)
        by (let _w := fresh "_w" in
            let _p := fresh "_p" in
            destruct h as [_w _p];
            let _h_f := fresh "_H" in
            intro _h_f;
            apply (_h_f _w);
            exact _p)
  end; cbv beta in newH.

Tactic Notation "_elim_exists_app" constr(h) constr(Q) ident(newH) constr(hpq) := 
  match type of h with
  | exists x, @?P x =>
      assert (newH : (forall x, P x -> Q) -> Q)
        by (let _w := fresh "_w" in
            let _p := fresh "_p" in
            destruct h as [_w _p];
            let _h_f := fresh "_H" in
            intro _h_f;
            apply (_h_f _w);
            exact _p)
  end; cbv beta in newH; apply newH in hpq.


Tactic Notation "_reflexivity" constr(x) ident(h) :=
  assert (h : x = x) by reflexivity.
