From Stdlib Require Import Arith Lia.
Require Import Decidability.




(*Suivant la suggestion de l’énoncé, on commence par définir <= dans le
langage de Peano.*)
Definition Le x y := exists z, x+z=y.

(*On montre que la définition alternative de <= est équivalente à celle qui
existe par défaut dans Coq. Par la suite, on pourra donc utiliser x <= y
comme s’il s’agissait de Le x y.*)
Lemma Le_is_le x y : Le x y <-> x <= y.
Proof.
  constructor; intro xley.
    destruct xley. lia.
    induction xley as [ | y xley Lexy].
      exists 0. lia.
      destruct Lexy as [z xpluszeqy]. exists (S z). lia.
Qed.




(*Comme on utilise les nombres premiers, on a évidemment besoin de la
divisibilité. On vérifie donc qu’elle est définie dans Coq comme une
formule de l’arithmétique de Peano.*)
(*Print Nat.divide.*)
(*Nat.divide = fun x y : nat => exists z : nat, y = z * x
     : nat -> nat -> Prop*)
(*Nat.divide est bien définie comme une formule de l’arithmétique de
Peano. On n’a donc pas besoin de définir une formule équivalente.
On lui définit aussi une notation par souci de lisibilité.*)
Infix "\" := Nat.divide (at level 70, no associativity).

(*On définit plus explicitement la divisibilité. On montre aussi que c’est
une propriété décidable pour plus tard.*)
Lemma divide_mul_div x y (xpos : x <> 0) : x \ y <-> x * (y / x) = y.
Proof.
  constructor; intro H.
  - destruct H as [z H].
    rewrite H.
    rewrite (Nat.div_mul _ _ xpos).
    apply Nat.mul_comm.
  - exists (y / x). lia.
Qed.

Lemma divide_dec x y : decidable (x \ y).
Proof.
  destruct x.
    destruct y.
      left. exists 0. lia.
      right. intro H. destruct H. lia.
  assert (Sxpos : S x <> 0) by (apply Nat.neq_succ_0).
  rewrite (divide_mul_div (S x) y Sxpos).
  lia.
Qed.




(*On introduit maintenant la définition de la primalité.*)
Definition prime p := 1 < p /\ forall d,  d \ p -> 1 < d -> d = p.

(*On veut prouver la forme suivante du théorème d’Euclide : ∀x∃p>x prime p
Pour cela, je compte utiliser la preuve suivante : pour tout x, x!+1 est
divisible par un nombre premier, mais pas par un nombre inférieur ou égal
à x, donc ce nombre premier est strictement supérieur à x.
J’ai donc besoin de deux lemmes : tout entier strictement supérieur à 1 est
divisible par un nombre premier, et pour y≤x, y \ x! (dont je déduirai que
y ne divise pas x!+1 si y est premier)*)

(*La preuve du premier lemme consiste à trouver le plus petit diviseur de
x qui soit supérieur à 1 et prouver que celui-ci est premier en utilisant
le fait que la relation de divisibilité est transitive.*)
Lemma exists_prime_divisor x (oneltx : 1 < x) :
  exists p, p \ x /\ prime p.
Proof.
  assert (smallest_divisor : exists d, 1 < d /\ d \ x).
    exists x. constructor.
      exact oneltx.
      apply Nat.divide_reflexive.
  apply smallest_element in smallest_divisor. shelve.
    intro. dec_simpl.
      lia.
      apply divide_dec.
  Unshelve.
  destruct smallest_divisor as [p H].
  destruct H as [H p_smallest].
  destruct H as [oneltp pdivx].  
  exists p.
  constructor.
    exact pdivx.
  constructor.
    exact oneltp.
  intros d ddivp oneltd.
  apply Nat.le_antisymm.
    apply Nat.divide_pos_le.
      lia.
      exact ddivp.
  apply p_smallest.
  constructor.
    exact oneltd.
    apply (Nat.divide_transitive _ p); assumption.
Qed.


(*Le second lemme est assez simple et se divise en plusieurs étapes:
on prouve d’abord par récurrence que pour x≤y, fact x \ fact y, puis que
si 0 < x, x \ fact x, et ces deux résultats donnent x \ fact y.*)
Lemma fact_divide_fact_succ x : fact x \ fact (S x).
Proof.
  exists (S x).
  reflexivity.
Qed.

Lemma fact_divide_fact_le x y (xley : x <= y) : fact x \ fact y.
Proof.
  apply <- Le_is_le in xley.
  destruct xley as [z xpluszeqy].
  rewrite <- xpluszeqy.
  clear dependent y.
  induction z.
  - rewrite Nat.add_0_r.
    apply Nat.divide_reflexive.
  - apply (Nat.divide_transitive _ (fact (x + z))).
      assumption.
      rewrite Nat.add_succ_r. apply fact_divide_fact_succ.
Qed.

Lemma divide_fact x (posx : 0 < x) : x \ fact x.
Proof.
  apply Nat.neq_0_lt_0 in posx.
  apply Nat.neq_0_r in posx as xsucc. clear posx.
  destruct xsucc as [y xeqSy].
  rewrite xeqSy.
  clear dependent x.
  exists (fact y).
  rewrite Nat.mul_comm.
  reflexivity.
Qed.

Lemma divide_fact_le x y (posx : 0 < x) (xley : x <= y) : x \ fact y.
Proof.
  apply (Nat.divide_transitive _ (fact x)).
    exact (divide_fact x posx).
    exact (fact_divide_fact_le x y xley).
Qed.


(*Il reste encore deux lemmes simples qui sont utilisés dans la preuve du
théorème d’Euclide.*)
Lemma two_is_prime : prime 2.
Proof.
  constructor.
  - apply le_n.
  - intros d ddiv2 onelt2.
    apply Nat.divide_pos_le in ddiv2; lia.
Qed.

Lemma succ_sub x : S x - x = 1.
(*Étonnamment, ce théorème n’est pas dans Arith.*)
Proof.
  lia.
Qed.


Theorem Euclid x : exists p, prime p /\ x < p.
Proof.
  destruct (exists_prime_divisor (S (fact x))) as [p H].
    apply -> Nat.succ_lt_mono. apply lt_O_fact.
  exists p.
  destruct H as [pdivSfactx primep].
  constructor.
    exact primep.
  destruct primep as [oneltp H]. clear H.
  apply Nat.lt_nge. intro plex.
  apply (divide_fact_le p x) in plex; [ | lia].
  apply (Nat.divide_sub_r _ _ _ pdivSfactx) in plex. clear pdivSfactx.
  rewrite succ_sub in plex.
  apply Nat.divide_1_r in plex. lia.
Qed.




(*Pour coder les suites d’entiers, j’utilise la première méthode suggérée
par l’énoncé, à savoir le codage en base première. On introduit donc la
notion de puissance de nombre premier.*)
Definition IsPrimePower p x := forall d, d \ x -> 1 < d -> p \ d.

(*Si p est un nombre premier, cette formule équivaut à
exists e, x = p ^ e.
Si p = 1 alors elle est vraie pour tous les entiers.
Si p admet deux diviseurs non premiers alors elle équivaut à x = 1.
Le premier cas est le seul qui m’intéresse, je vais donc prouver celui-ci.
Pour montrer IsPrimePower p x -> exists e, x = p ^ e, j’aurai besoin de
raisonner par récurrence forte: je montre que IsPrimePower p 0 est faux, 
que 1 = p ^ 0, puis que si 1 < x et IsPrimePower p x est vrai, alors p \ x,
dont je déduis que p = (p / x) * p; je montre ensuite que p / x < x et
qu’en tant que diviseur de x, on a IsPrimePower p (p / x), ce qui me permet
d’utiliser l’hypothèse de récurrence forte et de montrer que p / x = p ^ e
pour un certain e, dont je déduis x = p ^ S e.
Pour la réciproque, je raisonne par récurrence sur l’exposant e: 1 n’a
aucun diviseur supérieur à 1, donc IsPrimePower p 1, et si
IsPrimePower p (p^e), pour d \ p ^ S e, on montre d est premier avec p ou
p \ d. Dans le premier cas (absurde, mais on a justement besoin de ce
raisonnement pour le prouver), d \ p ^ e et par hypothèse de récurrence,
p \ d; quant au second, c’est exactement notre objectif.*)

Lemma OIsNotPrimePower p (primep : prime p) : ~ IsPrimePower p 0.
Proof.
  intro OIsPP.
  destruct primep as [oneltp ncompp]. clear ncompp.
  assert (Spdiv0 : S p \ 0) by (apply Nat.divide_0_r).
  assert (oneltSp : 1 < S p) by lia.
  apply (OIsPP _ Spdiv0) in oneltSp. clear Spdiv0 OIsPP.
  assert (pdivp : p \ p) by (apply Nat.divide_reflexive).
  apply (Nat.divide_sub_r _ _ _ oneltSp) in pdivp. clear oneltSp.
  rewrite succ_sub in pdivp.
  apply Nat.divide_1_r in pdivp. lia.
Qed.

Lemma PrimeDividesPrimePowers p x (oneltx : 1 < x)
  (xIsPP : IsPrimePower p x) : p \ x.
Proof.
  apply xIsPP.
    apply Nat.divide_reflexive.
    exact oneltx.
Qed.

Lemma DivisorsArePrimePowers p x d
  (xIsPP : IsPrimePower p x) (ddivx : d \ x) :
    IsPrimePower p d.
Proof.
  intros d' d'divd oneltd'.
  apply xIsPP.
    apply (Nat.divide_transitive _ d); assumption.
    exact oneltd'.
Qed.

Lemma PrimeIsCoprimeOrDivides p x (primep : prime p) :
  Nat.gcd x p = 1 \/ p \ x.
Proof.
  destruct primep as [oneltp ncompp].
  assert (gcddivp : Nat.gcd x p \ p) by (apply Nat.gcd_divide_r).
  destruct (le_lt_dec (Nat.gcd x p) 1) as [gcdle1 | oneltgcd].
  - left. destruct gcddivp. lia.
  - right. apply Nat.divide_gcd_iff.
    rewrite Nat.gcd_comm. apply ncompp; assumption.
Qed.

Lemma IsPrimePower_works p x (primep : prime p) :
  IsPrimePower p x <-> exists e, x = p ^ e.
Proof.
  constructor; intro xIsPP.
  - revert xIsPP.
    strong_induction x.
      intro OIsPP. exfalso. apply (OIsNotPrimePower p); assumption.
    intros IHx SxIsPP.
    destruct x.
      exists 0. reflexivity.
    set (x' := S (S x)).
    assert (oneltx' : 1 < x') by lia.
    assert (pdivx' : p \ x') by
      (apply (PrimeDividesPrimePowers p x'); assumption).
    destruct primep as [oneltp ncompp]. clear ncompp.
    apply divide_mul_div in pdivx'; [ | lia].
    assert (x'pleSx : x' / p <= S x).
      apply le_S_n.
      apply Nat.div_lt.
        lia.
        exact oneltp.
    clear oneltp oneltx'.
    assert (x'IsPP : IsPrimePower p (x' / p)).
      apply (DivisorsArePrimePowers p x' (x' / p)).
        exact SxIsPP.
        exists p. lia.
    clear SxIsPP.
    apply (IHx _ x'pleSx) in x'IsPP. clear IHx x'pleSx.
    destruct x'IsPP as [e x'peqpe].
    exists (S e). simpl. lia.
  - destruct xIsPP as [e xeqpe].
    rewrite xeqpe. clear dependent x.
    intros d ddivx oneltd.
    induction e; simpl in *.
      apply Nat.divide_pos_le in ddivx; lia.
    rename ddivx into ddivpx.
    destruct (PrimeIsCoprimeOrDivides p d primep) as [pcoprd | pdivd].
    + apply (Nat.gauss _ _ _ ddivpx) in pcoprd as ddivx.
      apply IHe.
      exact ddivx.
    + exact pdivd.
Qed.

Lemma p_ToThe_e_IsPrimePower p e (primep : prime p) :
  IsPrimePower p (p ^ e).
Proof.
  apply IsPrimePower_works.
    exact primep.
    exists e. reflexivity.
Qed.




(*Maintenant qu’on a codé les puissances de nombres premiers, on peut
parler des codages en base p. On commence par la formule DIG, qui a pour
propriété que si c = Σ d_n * p ^ n avec d_n < p pour tout n, alors
IsNithDigit p (p ^ e) c d sera vrai si et seulement si d = d_e.*)
Definition IsNthDigit p Pop c d :=
  d < p /\ exists a, a < Pop /\ exists b, c = b * p * Pop + d * Pop + a.
(*Moyen mnémotechnique pour retenir le rôle de chaque variable:
p = prime
Pop = Power of p
c = code
d = digit*)

(*On commence par donner explicitement les valeurs du a et du b dans la
définition de IsNthDigit pour simplifier les futures preuves.*)
Lemma IsNthDigit_explicit p Pop c d (primep : prime p)
  (PopIsPP : IsPrimePower p Pop) :
    IsNthDigit p Pop c d <->
    c = c / (p * Pop) * p * Pop + d * Pop + c mod Pop.
Proof.
  constructor; intro H.
  - destruct H as [dltp H].
    destruct H as [a H].
    destruct H as [altPop H].
    destruct H as [b value_of_c].
    assert (value_of_a : a = c mod Pop).
      apply (Nat.mod_unique _ _ (b * p + d)).
        exact altPop.
      lia.
    rewrite value_of_a in *. clear dependent a.
    assert (value_of_b : b = c / (p * Pop)).
      apply (Nat.div_unique _ _ _ (d * Pop + c mod Pop)).
        apply (Nat.lt_le_trans _ (S d * Pop)).
          simpl. lia.
        apply Nat.mul_le_mono_r. exact dltp.
      lia.
    lia.
  - assert (Popne0 : Pop <> 0).
      intro Popeq0. rewrite Popeq0 in *. clear dependent Pop.
      apply (OIsNotPrimePower p primep). exact PopIsPP.
    constructor.
    + apply (Nat.mul_lt_mono_pos_r Pop).
        apply Nat.neq_0_lt_0. exact Popne0.
      apply (Nat.le_lt_trans _ (c mod (p * Pop))).
        rewrite Nat.Div0.mod_eq. lia.
      apply Nat.mod_upper_bound. apply -> Nat.neq_mul_0. constructor.
        apply Nat.neq_0_lt_0. destruct primep. lia.
        exact Popne0.
    + exists (c mod Pop).
      constructor.
      * apply Nat.mod_upper_bound. exact Popne0.
      * exists (c / (p * Pop)). exact H.
Qed.

(*On reformule ensuite IsNthDigit_explicit sous une forme plus facile à
utiliser. Je choisis d’utiliser une forme qui n’utilise que la fonction
modulo car si c = Σ d_n * p ^ n, alors c mod (p ^ e) est la somme partielle
d_0 + d_1 * p + … + d_{e-1} * p ^ (e - 1) (on le prouvera juste après)*)
Lemma IsNthDigit_mod p Pop c d (primep : prime p)
  (PopIsPP : IsPrimePower p Pop) :
    IsNthDigit p Pop c d <->
    c mod (p * Pop) = d * Pop + c mod Pop.
Proof.
  rewrite IsNthDigit_explicit; try assumption.
  rewrite (Nat.div_mod_eq c (p * Pop)) at 1.
  lia.
Qed.

(*On introduit maintenant le codage en base p.*)
Fixpoint encoding p f x := match x with
| 0 => f 0
| S y => f x * p ^ x + encoding p f y
end.

(*Je montre d’abord par récurrence que pour tout x,
encoding p f x < p * p ^ x (dont un corollaire immédiat est
encoding p f x mod p ^ S x = encoding p f x).
Le raisonnement est classique: encoding p f 0 = f 0 < p et si
encoding p f x < p * p ^ x alors
encoding p f (S x) = f (S x) * p ^ (S x) + encoding p f x
  < f (S x) * p ^ (S x) + p ^ S x <= p * p ^ (S x) (car f (S x) < p).
Je fais le choix d’écrire p * p ^ x plutôt que p ^ S x pour deux raisons:
1. Cette forme est plus facilement accessible grâce à la tactique simpl.
2. Elle est plus compatible avec la notation p * Pop qu’on utilise avec les
puissances de p «inconnues».*)
Lemma encoding_small p f x (p_large_enough : forall y, y <= x -> f y < p) :
  encoding p f x < p * p ^ x.
Proof.
  induction x; simpl in *.
  - rewrite Nat.mul_1_r. apply p_large_enough. apply le_n.
  - assert (IHx_ant : forall y, y <= x -> f y < p).
      intros y ylex. apply p_large_enough. apply le_S. exact ylex.
    assert (IHx := IHx IHx_ant). clear IHx_ant.
    apply (Nat.lt_le_trans _ ((f (S x) + 1) * (p * p ^ x))).
    + rewrite Nat.mul_add_distr_r.
      apply Nat.add_lt_mono_l.
      rewrite Nat.mul_1_l.
      exact IHx.
    + apply Nat.mul_le_mono_r.
      rewrite Nat.add_1_r.
      apply p_large_enough.
      apply le_n.
Qed.

(*Je peux maintenant prouver l’affirmation que je faisais aux lignes
363-364 sous une forme rigoureuse : si c = f 0 + f 1 * p + … + f z * p ^ z
(c’est-à-dire encoding p f z), alors c mod p ^ S e = encoding p f e
(encore une fois je privilégie la notation p * p ^ e à p ^ S e).
Encore une fois c’est un raisonnement par récurrence simple sur y:=z-e:
encoding p f e mod (p * p ^ e) = encoding p f e d’après encoding_small,
et après cela on n’ajoute que des nombres divisibles par p * p ^ e.
J’anticipe déjà sur le théorème final en choisissant la notation*)
Lemma encoding_mod p f z e (elez : e <= z)
  (p_large_enough : forall e', e' <= e -> f e' < p) :
    encoding p f z mod (p * p ^ e) = encoding p f e.
Proof.
  apply Le_is_le in elez.
  destruct elez as [y eyeqz].
  rewrite <- eyeqz in *. clear dependent z.
  induction y.
  - rewrite Nat.add_0_r.
    apply Nat.mod_small.
    apply encoding_small. exact p_large_enough.
  - rewrite Nat.add_succ_r. simpl in *.
    rewrite <- IHy.
    clear IHy.
    rewrite <- Nat.Div0.add_mod_idemp_l.
    f_equal.
    assert (H : f (S (e + y)) * (p * p ^ (e + y)) =
                f (S (e + y)) * p ^ y * (p * p ^ e)).
      rewrite Nat.pow_add_r. lia.
    rewrite H. clear H.
    rewrite Nat.Div0.mod_mul.
    reflexivity.
Qed.

(*Je déduis du théorème précédent et de la formule donnée par
IsNthDigit_mod que f e est bien reconnu par IsNthDigit comme voulu:
encoding p f z mod p = encoding p f 0 = f 0 = f 0 + encoding p f z mod 1
et pour e > 0,
encoding p f z mod (p * p ^ e) = encoding p f e
                               = f e + encoding p f (e-1)
                               = f e + encoding p f (e-1) mod p ^ e*)
Lemma encoding_works p f z e (primep : prime p) (elez : e <= z)
  (p_large_enough : forall e', e' <= e -> f e' < p) :
    IsNthDigit p (p ^ e) (encoding p f z) (f e).
Proof.
  apply IsNthDigit_mod.
    exact primep.
    apply p_ToThe_e_IsPrimePower. exact primep.
  rewrite encoding_mod; try assumption.
  destruct e; simpl.
    lia.
  apply Nat.lt_le_incl in elez.
  apply Nat.add_cancel_l.
  apply eq_sym.
  apply encoding_mod.
    exact elez.
  intros e' e'lee.
  apply p_large_enough.
  lia.
Qed.


(*De plus, IsNthDigit_mod montre aussi clairement qu’il ne peut pas y avoir
d’autre candidat que d := f e comme solution de
IsNthDigit p f (encoding p f z) d*)
Lemma NthDigitIsUnique p Pop c d1 d2 (primep : prime p)
  (PopIsPP : IsPrimePower p Pop) (d1IsNthDigit : IsNthDigit p Pop c d1)
  (d2IsNthDigit : IsNthDigit p Pop c d2) :
    d1 = d2.
Proof.
  rewrite IsNthDigit_mod in d1IsNthDigit; try assumption.
  rewrite IsNthDigit_mod in d2IsNthDigit; try assumption.
  rewrite d1IsNthDigit in d2IsNthDigit.
  clear d1IsNthDigit. rename d2IsNthDigit into d1eqd2.
  apply Nat.add_cancel_r in d1eqd2.
  apply Nat.mul_cancel_r in d1eqd2.
    exact d1eqd2.
  intro Popeq0. rewrite Popeq0 in *.
  apply (OIsNotPrimePower p); assumption.
Qed.

Lemma digit_value p f z e d (primep : prime p) (elez : e <= z)
  (p_large_enough : forall e', e' <= e -> f e' < p)
  (dIsNthDigit : IsNthDigit p (p ^ e) (encoding p f z) d) :
    d = f e.
Proof.
  apply (NthDigitIsUnique p (p ^ e) (encoding p f z)).
    exact primep.
    apply p_ToThe_e_IsPrimePower. exact primep.
    exact dIsNthDigit.
    apply encoding_works; assumption.
Qed.




(*On introduit enfin IsNthPowerOf x y z :<-> x = y ^ z*)
Definition IsNthPowerOf x y z := exists p c1 c2,
    prime p /\ IsNthDigit p 1 c1 1 /\ IsNthDigit p 1 c2 1 /\
    (forall d Pop, p * Pop <= c2 -> IsPrimePower p Pop ->
      (IsNthDigit p Pop c1 d -> IsNthDigit p (p * Pop) c1 (y * d))) /\
    (forall d Pop, p * Pop <= c2 -> IsPrimePower p Pop ->
      (IsNthDigit p Pop c2 d -> IsNthDigit p (p * Pop) c2 (S d))) /\
    exists Pop, Pop <= c2 /\ IsPrimePower p Pop /\
      IsNthDigit p Pop c1 x /\ IsNthDigit p Pop c2 (S z).
(*L’idée de cette définition, qui sera reprise à l’identique dans la preuve
qu’elle fonctionne, est la suivante: si x = y ^ z, alors on peut la coder
dans une base première assez grande comme une suite [1; y; … ; y^z],
(donnée par la valeur initiale 1 et la relation de récurrence
IsNthDigit p (p ^ k) d c1 -> IsNthDigit p (p ^ (S k)) (y * d) c1), et on
veut identifier que x est le z-ème terme de cette suite, ce qu’on ne peut
pas faire directement, donc on utilise une deuxième suite commençant par
[1; … ; z; z+1] et on demande que x soit présent au même rang que z+1.
Notons qu’on choisit que la seconde suite aille de 1 à z+1 plutôt que de 0
à z pour ne pas être gênés par le cas z=0 : en effet, du point de vue du
codage en base p, une suite qui se termine par un 0 est identique à une
suite plus courte, or on utilise la comparaison avec c2 comme référence
pour s’assurer qu’on traite bien des indices valides donc il n’est pas
souhaitable qu’il y ait des valeurs nulles dans celle-ci.*)

Theorem IsNthPowerOf_works x y z : IsNthPowerOf x y z <-> x = y ^ z.
(*La preuve est longue (en Coq) mais naturelle:
- si IsNthPowerOf x y z est vraie, alors on prouve par récurrence que pour
tout indice valide e, le e-ème terme de la suite c1 est y ^ e et celui de
la suite c2 est S e, et de plus, il existe un e tel que le e-ème terme de
c1 soit x et le e-ème terme de c2 soit S z, dont on déduit x = y ^ e et
e = z, d’où le résultat.
- si x = y ^ z, alors on code dans une base première p assez grande les
suites c1:=[1; y; …; y ^ z] et c2:=[1; …; z+1]. On montre ensuite chacune
des assertions de IsNthPowerOf x y z : que les valeurs initiales sont
correctes, que p ^ e <= c2 implique e <= z, dont on déduit la relation de
récurrence, puis que p ^ z est une puissance de p inférieure à c2 et que
IsNthDigit p (p ^ z) c1 (y ^ z) et IsNthDigit p (p ^ z) c2 (S z).*)
Proof.
  constructor; intro xisytothez.
  - destruct xisytothez as [p H].
    destruct H as [c1 H].
    destruct H as [c2 H].
    destruct H as [primep H].
    destruct H as [c1_init H].
    destruct H as [c2_init H].
    destruct H as [heredity1 H].
    destruct H as [heredity2 H].

    assert (c1_works : forall e, (p ^ e) <= c2 ->
      IsNthDigit p (p ^ e) c1 (y ^ e)).
      intros e pelec2; induction e; simpl in *.
        exact c1_init.
      assert (peIsPP := p_ToThe_e_IsPrimePower p e primep).
      apply heredity1; try assumption.
      apply IHe.
      apply (Nat.le_trans _ (p * p ^ e)).
        rewrite <- Nat.mul_1_l at 1.
        apply Nat.mul_le_mono_r.
        destruct primep.
        lia.
      exact pelec2.
    clear c1_init heredity1.

    assert (c2_works : forall e, (p ^ e) <= c2 ->
      IsNthDigit p (p ^ e) c2 (S e)).
      intros e pelec2; induction e; simpl in *.
        exact c2_init.
      assert (peIsPP := p_ToThe_e_IsPrimePower p e primep).
      apply heredity2; try assumption.
      apply IHe.
      apply (Nat.le_trans _ (p * p ^ e)).
        rewrite <- Nat.mul_1_l at 1.
        apply Nat.mul_le_mono_r.
        destruct primep. lia.
      exact pelec2.
    clear c2_init heredity2.

    destruct H as [Pop H].
    destruct H as [Poplec2 H].
    destruct H as [PopIsPP H].
    apply IsPrimePower_works in PopIsPP as explicitPop; try assumption.
    destruct explicitPop as [e Popeqpe].
    rewrite Popeqpe in *. clear dependent Pop.
    assert (c1_works := c1_works e Poplec2).
    assert (c2_works := c2_works e Poplec2).
    destruct H as [xIsNthDigitc1 zIsNthDigitc2].
    apply (NthDigitIsUnique p (p ^ e) c1); try assumption.
    enough (zeqe : z = e). rewrite zeqe. assumption.
    apply eq_add_S.
    apply (NthDigitIsUnique p (p ^ e) c2); try assumption.

  - rewrite xisytothez. clear dependent x.
    destruct (Euclid (max (y ^ z) (S z))) as [p H].
    destruct H as [primep xSzltp].
    apply Nat.max_lub_lt_iff in xSzltp.
    destruct xSzltp as [xltp Szltp].

    (*On vérifie ici qu’on a bien pris un p assez grand pour faire un
    codage correct.*)
    assert (powyltp : forall e, e <= z -> y ^ e < p).
      intros e elez.
      destruct (Nat.eq_dec y 0) as [yeq0 | yne0].
        rewrite yeq0 in *. clear dependent y.
        apply (Nat.le_lt_trans _ 1).
          destruct (Nat.eq_dec e 0) as [eeq0 | ene0].
            rewrite eeq0. apply le_n.
            rewrite Nat.pow_0_l. lia. exact ene0.
          destruct primep as [oneltp ncompp]. exact oneltp.
      apply (Nat.le_lt_trans _ (y ^ z)).
        apply Nat.pow_le_mono_r; assumption.
        exact xltp.

        exists p.
    set (c1 := encoding p (Nat.pow y) z).
    exists c1.
    set (c2 := encoding p S z).
    exists c2.

    constructor.
      exact primep.

    constructor.
      rewrite <- (Nat.pow_0_r y) at 2.
      apply encoding_works.
        exact primep.
        apply Nat.le_0_l.
      intros e' e'le0.
      apply powyltp.
      lia.

    constructor.
      apply encoding_works.
        exact primep.
        apply Nat.le_0_l.
      lia.

    assert (length_is_z : forall e, p ^ e <= c2 -> e <= z).
      intros e pelec2.
        apply le_S_n.
        destruct primep as [oneltp ncompp].
        apply (Nat.pow_lt_mono_r_iff p).
          exact oneltp.
        apply (Nat.le_lt_trans _ c2).
          exact pelec2.
        apply encoding_small.
        lia.

    constructor.
      intros d Pop pPoplec2 PopIsPP dIsNthDigit.
      apply IsPrimePower_works in PopIsPP; [ | exact primep].
      destruct PopIsPP as [e Popeqpe].
      rewrite Popeqpe in *. clear dependent Pop.
      apply (length_is_z (S e)) in pPoplec2 as Selez. 
      assert (deqye : d = y ^ e).
        apply (digit_value p _ z); try assumption.
          lia.
          intros e' e'lee. apply powyltp. lia.
      rewrite deqye in *. clear dependent d.
      rewrite <- (Nat.pow_succ_r' y).
      apply encoding_works; try assumption.
      intros e' e'lSe. apply powyltp. lia.

    constructor.
      intros d Pop pPoplec2 PopIsPP dIsNthDigit.
      apply IsPrimePower_works in PopIsPP; [ | exact primep].
      destruct PopIsPP as [e Popeqpe].
      rewrite Popeqpe in *. clear dependent Pop.
      apply (length_is_z (S e)) in pPoplec2 as Selez. 
      assert (deqSe : d = S e).
        apply (digit_value p S z); (assumption || lia).
      rewrite deqSe in *. clear dependent d.
      apply (encoding_works _ S _ (S e)); (assumption || lia).

    exists (p ^ z).
    constructor.
      destruct z; unfold c2; simpl.
        apply le_n.
        rewrite <- Nat.add_assoc. apply Nat.le_add_r.
    constructor.
      apply p_ToThe_e_IsPrimePower. exact primep.
    constructor; apply encoding_works; (assumption || lia).
Qed.

(*Le principe se généralise sans peine à n’importe quel schéma de
récurrence, quoiqu’il demande une preuve similairement longue (mais plus
facile à rédiger en recopiant et adaptant le travail déjà fait):*)
Definition y_Is_f_Of_x f frec x y := exists p c1 c2,
    prime p /\ IsNthDigit p 1 c1 (f 0) /\ IsNthDigit p 1 c2 1 /\
    (forall d1 d2 Pop, p * Pop <= c2 -> IsPrimePower p Pop ->
      (IsNthDigit p Pop c1 d1 -> IsNthDigit p Pop c2 (S d2) ->
        IsNthDigit p (p * Pop) c1 (frec d1 d2))) /\
    (forall d, forall Pop, p * Pop <= c2 -> IsPrimePower p Pop ->
      (IsNthDigit p Pop c2 d -> IsNthDigit p (p * Pop) c2 (S d))) /\
    exists Pop, Pop <= c2 /\ IsPrimePower p Pop /\
      IsNthDigit p Pop c1 y /\ IsNthDigit p Pop c2 (S x).

Fixpoint max_f f x := match x with
| 0 => f 0
| S y => max (f x) (max_f f y)
end.

Lemma max_f_is_max f x p (p_large : max_f f x < p) :
  forall e, e <= x -> f e < p.
Proof.
  intros e elex.
  induction x; simpl in *.
  - apply Nat.le_0_r in elex. rewrite elex. exact p_large.
  - apply Nat.max_lub_lt_iff in p_large.
    destruct p_large as [fSxltp p_large].
    apply Nat.le_lteq in elex.
    destruct elex as [elex | eeqSx].
      apply -> Nat.lt_succ_r in elex. apply IHx; assumption.
      rewrite eeqSx in *. assumption.
Qed.

Theorem y_Is_f_Of_x_works f frec x y
  (frec_works : forall z, f (S z) = frec (f z) z) :
    y_Is_f_Of_x f frec x y <-> y = f x.
Proof.
  constructor; intro yisfofx.
  - destruct yisfofx as [p H].
    destruct H as [c1 H].
    destruct H as [c2 H].
    destruct H as [primep H].
    destruct H as [c1_init H].
    destruct H as [c2_init H].
    destruct H as [heredity1 H].
    destruct H as [heredity2 H].

    assert (c2_works : forall e, (p ^ e) <= c2 ->
      IsNthDigit p (p ^ e) c2 (S e)).
      intros e pelec2; induction e; simpl in *.
        exact c2_init.
      assert (peIsPP := p_ToThe_e_IsPrimePower p e primep).
      apply heredity2; try assumption.
      apply IHe.
      apply (Nat.le_trans _ (p * p ^ e)).
        rewrite <- Nat.mul_1_l at 1.
        apply Nat.mul_le_mono_r.
        destruct primep. lia.
      exact pelec2.
    clear c2_init heredity2.

    assert (c1_works : forall e, (p ^ e) <= c2 ->
      IsNthDigit p (p ^ e) c1 (f e)).
      intros e pelec2; induction e; simpl in *.
        exact c1_init.
      rewrite frec_works.
      rename pelec2 into ppelec2.
      assert (pelec2 : p ^ e <= c2).
        apply (Nat.le_trans _ (p * p ^ e)).
          rewrite <- Nat.mul_1_l at 1.
          apply Nat.mul_le_mono_r.
          destruct primep.
          lia.
        exact ppelec2.
      apply heredity1.
          exact ppelec2.
          apply p_ToThe_e_IsPrimePower. exact primep.
        apply IHe.
        exact pelec2.
      apply c2_works.
      exact pelec2.
    clear c1_init heredity1.

    destruct H as [Pop H].
    destruct H as [Poplec2 H].
    destruct H as [PopIsPP H].
    apply IsPrimePower_works in PopIsPP as explicitPop; try assumption.
    destruct explicitPop as [e Popeqpe].
    rewrite Popeqpe in *. clear dependent Pop.
    assert (c1_works := c1_works e Poplec2).
    assert (c2_works := c2_works e Poplec2).
    destruct H as [xIsNthDigitc1 zIsNthDigitc2].
    apply (NthDigitIsUnique p (p ^ e) c1); try assumption.
    enough (xeqe : x = e). rewrite xeqe. assumption.
    apply eq_add_S.
    apply (NthDigitIsUnique p (p ^ e) c2); try assumption.

  - rewrite yisfofx. clear dependent y.
    destruct (Euclid (max (max_f f x) (S x))) as [p H].
    destruct H as [primep p_large].
    apply Nat.max_lub_lt_iff in p_large.
    destruct p_large as [p_large Sxltp].
    assert (fltp := max_f_is_max f x p p_large). clear p_large.
    exists p.
    set (c1 := encoding p f x).
    exists c1.
    set (c2 := encoding p S x).
    exists c2.

    constructor.
      exact primep.

    constructor.
      apply encoding_works.
        exact primep.
        apply Nat.le_0_l.
      intros e ele0.
      apply fltp.
      lia.

    constructor.
      apply encoding_works.
        exact primep.
        apply Nat.le_0_l.
      lia.

    assert (length_is_x : forall e, p ^ e <= c2 -> e <= x).
      intros e pelec2.
        apply le_S_n.
        destruct primep as [oneltp ncompp].
        apply (Nat.pow_lt_mono_r_iff p).
          exact oneltp.
        apply (Nat.le_lt_trans _ c2).
          exact pelec2.
        apply encoding_small.
        lia.

    constructor.
      intros d1 d2 Pop pPoplec2 PopIsPP d1IsNthDigit d2IsNthDigit.
      apply IsPrimePower_works in PopIsPP; [ | exact primep].
      destruct PopIsPP as [e Popeqpe].
      rewrite Popeqpe in *. clear dependent Pop.
      apply (length_is_x (S e)) in pPoplec2 as Selez. 
      assert (d1eqfe : d1 = f e).
        apply (digit_value p _ x); try assumption.
          lia.
          intros e' e'lee. apply fltp. lia.
      rewrite d1eqfe in *. clear dependent d1.
      assert (d2eqe : d2 = e).
        apply eq_add_S.
        apply (digit_value p _ x); try assumption.
          lia.
          intros e' e'lee. lia.
      rewrite d2eqe in *. clear dependent d2.
      rewrite <- frec_works.
      apply encoding_works; try assumption.
      intros e' e'lSe. apply fltp. lia.

    constructor.
      intros d Pop pPoplec2 PopIsPP dIsNthDigit.
      apply IsPrimePower_works in PopIsPP; [ | exact primep].
      destruct PopIsPP as [e Popeqpe].
      rewrite Popeqpe in *. clear dependent Pop.
      apply (length_is_x (S e)) in pPoplec2 as Selez. 
      assert (deqSe : d = S e).
        apply (digit_value p S x); (assumption || lia).
      rewrite deqSe in *. clear dependent d.
      apply (encoding_works _ S _ (S e)); (assumption || lia).

    exists (p ^ x).
    constructor.
      destruct x; unfold c2; simpl.
        apply le_n.
        rewrite <- Nat.add_assoc. apply Nat.le_add_r.
    constructor.
      apply p_ToThe_e_IsPrimePower. exact primep.
    constructor; apply encoding_works; (assumption || lia).
Qed.