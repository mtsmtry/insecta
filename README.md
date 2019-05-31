# 定理証明言語LightMath(仮)

## まだできてません
実装はほとんどできましたが、デバッグが終わっておらず、現状は0*1=0くらいしか証明できません。
しかし、以下のような仕様になる予定です。

## Coqよりも簡単に証明ができます
例えば、極限がある数に収束する関数同士の積の極限はその数の積に収束するという定理は、以下のように記述できます。
項書き換え系を用いてある程度自動化されているので、基本的に式を同値変形するだけで証明できます。

- LightMath
```
theorem (a, b: R) (f: Converge(a), g: Converge(b)) {
	n->f[n] * g[n]: Converge(a * b)
proof:
	let M = max(max(f, g))
	context f.Converge(a) & g.Converge(b)
	unfold n >= n_1 -> dist(a, f(n)) < eps/(2*M) & n >= n_2 -> dist(b, g(n)) < eps/(2*abs(a)+1)
	impl assume n >= n_1 & n >= n_2 {
		start dist(a, f(n)) < eps/(2*M) & dist(b, g(n)) < eps/(2*abs(a)+1)
		impl dist(a*b, f(n)*g(n)) <= abs(a*(b-g(n))) + abs(g(n)*(a-f(n)))
		step dist(a*b, f(n)*g(n)) <= abs(a)*dist(b, g(n)) + abs(g(n))*dist(a, f(n))
		step dist(a*b, f(n)*g(n)) <= eps
	}
}
```
- Coq　
[Coq Standard Library](https://github.com/coq/coq/blob/master/theories/Reals/Rlimit.v)から引用
```
Lemma limit_mul :
  forall (f g:R -> R) (D:R -> Prop) (l l' x0:R),
    limit1_in f D l x0 ->
    limit1_in g D l' x0 -> limit1_in (fun x:R => f x * g x) D (l * l') x0.
Proof.
  intros; unfold limit1_in; unfold limit_in; simpl;
    intros;
      elim (H (Rmin 1 (eps * mul_factor l l')) (mul_factor_gt_f eps l l' H1));
        elim (H0 (eps * mul_factor l l') (mul_factor_gt eps l l' H1));
          clear H H0; simpl; intros; elim H; elim H0;
            clear H H0; intros; split with (Rmin x1 x); split.
  exact (Rmin_Rgt_r x1 x 0 (conj H H2)).
  intros; elim H4; clear H4; intros; unfold R_dist;
    replace (f x2 * g x2 - l * l') with (f x2 * (g x2 - l') + l' * (f x2 - l)).
  cut (Rabs (f x2 * (g x2 - l')) + Rabs (l' * (f x2 - l)) < eps).
  cut
    (Rabs (f x2 * (g x2 - l') + l' * (f x2 - l)) <=
      Rabs (f x2 * (g x2 - l')) + Rabs (l' * (f x2 - l))).
  exact (Rle_lt_trans _ _ _).
  exact (Rabs_triang _ _).
  rewrite (Rabs_mult (f x2) (g x2 - l')); rewrite (Rabs_mult l' (f x2 - l));
    cut
      ((1 + Rabs l) * (eps * mul_factor l l') + Rabs l' * (eps * mul_factor l l') <=
        eps).
  cut
    (Rabs (f x2) * Rabs (g x2 - l') + Rabs l' * Rabs (f x2 - l) <
      (1 + Rabs l) * (eps * mul_factor l l') + Rabs l' * (eps * mul_factor l l')).
  exact (Rlt_le_trans _ _ _).
  elim (Rmin_Rgt_l x1 x (R_dist x2 x0) H5); clear H5; intros;
    generalize (H0 x2 (conj H4 H5)); intro; generalize (Rmin_Rgt_l _ _ _ H7);
      intro; elim H8; intros; clear H0 H8; apply Rplus_lt_le_compat.
  apply Rmult_ge_0_gt_0_lt_compat.
  apply Rle_ge.
  exact (Rabs_pos (g x2 - l')).
  rewrite (Rplus_comm 1 (Rabs l)); unfold Rgt; apply Rle_lt_0_plus_1;
    exact (Rabs_pos l).
  unfold R_dist in H9;
    apply (Rplus_lt_reg_l (- Rabs l) (Rabs (f x2)) (1 + Rabs l)).
  rewrite <- (Rplus_assoc (- Rabs l) 1 (Rabs l));
    rewrite (Rplus_comm (- Rabs l) 1);
      rewrite (Rplus_assoc 1 (- Rabs l) (Rabs l)); rewrite (Rplus_opp_l (Rabs l));
        rewrite (proj1 (Rplus_ne 1)); rewrite (Rplus_comm (- Rabs l) (Rabs (f x2)));
          generalize H9; cut (Rabs (f x2) - Rabs l <= Rabs (f x2 - l)).
  exact (Rle_lt_trans _ _ _).
  exact (Rabs_triang_inv _ _).
  generalize (H3 x2 (conj H4 H6)); trivial.
  apply Rmult_le_compat_l.
  exact (Rabs_pos l').
  unfold Rle; left; assumption.
  rewrite (Rmult_comm (1 + Rabs l) (eps * mul_factor l l'));
    rewrite (Rmult_comm (Rabs l') (eps * mul_factor l l'));
      rewrite <-
        (Rmult_plus_distr_l (eps * mul_factor l l') (1 + Rabs l) (Rabs l'))
        ; rewrite (Rmult_assoc eps (mul_factor l l') (1 + Rabs l + Rabs l'));
          rewrite (Rplus_assoc 1 (Rabs l) (Rabs l')); unfold mul_factor;
            rewrite (Rinv_l (1 + (Rabs l + Rabs l')) (mul_factor_wd l l'));
              rewrite (proj1 (Rmult_ne eps)); apply Req_le; trivial.
  ring.
Qed.
```