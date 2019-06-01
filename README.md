# 定理証明言語Insecta(仮)

## 進捗状況
- [x] 字句解析
- [x] 字句解析エラーメッセージ
- [x] 構文解析
- [ ] 構文解析エラーメッセージ
- [x] 単一化
- [x] 簡略化
- [x] 導出
- [ ] 書き換えのマージ
- [ ] 書き換えの書き出し
- [ ] 定義の展開
- [ ] 篩型の展開
- [ ] let文
- [ ] assume文
- [ ] exists抽象化
- [ ] forall具象化
- [ ] 型付け型命題

## マクロ進捗状況
- [ ] 処理系の完成
- [ ] APIの完成
- [ ] Webサービスの完成
- [ ] 杉浦著解析入門Iの形式化
- [ ] Coqのライブラリに相当する程度の証明の完了
- [ ] インタラクティブな教科書の完成

## Coqよりも簡単に証明ができます
例えば、極限がある数に収束する関数同士の積の極限はその数の積に収束するという定理は、以下のように記述できます。
項書き換え系を用いてある程度自動化されているので、基本的に式を同値変形するだけで証明できます。

- LightMath
```
theorem (a, b: R) (f: Converge(a), g: Converge(b)) {
    n->f[n] * g[n]: Converge(a * b)
proof:
    let M = max(f, g)
    forall eps: R
    context f.Converge(a) & g.Converge(b)
    unfold n >= n_1 -> dist(a, f(n)) < eps/(2*M) & n >= n_2 -> dist(b, g(n)) < eps/(2*abs(a)+1)
    impl assume n >= n_1 & n >= n_2 {
        start dist(a, f(n)) < eps/(2*M) & dist(b, g(n)) < eps/(2*abs(a)+1)
        where dist(a*b, f(n)*g(n)) <= $ {
            impl abs(a*(b-g(n))) + abs(g(n)*(a-f(n)))
            step abs(a)*dist(b, g(n)) + abs(g(n))*dist(a, f(n))
            step eps
        }
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

# 文法
## 演算子定義
次のように`<キーワード> 優先順位 記号`によって演算子を定義できます。
```
unaryr 11 -
infixl 10 ^
infixl 9  *
infixl 9  /
infixl 8  +
infixl 8  -
```
演算子を定義するキーワードは、引数に取る項の数と結合性によって次の4種類があります。
| 演算子 | 結合性 | キーワード |
---|---|---
| 単項演算子 | 左結合 | infixl |
| 単項演算子 | 右結合 | infixr |
| 二項演算子 | 左結合 | unaryl |
| 二項演算子 | 右結合 | unaryr |

## 未定義語の宣言
次にように`undef 識別子: 型`によって未定義語を宣言できます。
```
undef R: Type
```
識別子に記号を使用する場合は、記号の前に`operator`キーワードを記述します。
また、宣言の後にオプションで`latex 文字列`と記述することで、LaTeXを出力する際の文字列を設定できます。
```
undef operator +: (N, N)->N 		  latex "+" 
undef operator *: (N, N)->N 		  latex "\cdot"
undef operator &: (Prop, Prop)->Prop  latex "\land"
undef operator |: (Prop, Prop)->Prop  latex "\lor"
```
LaTeX出力において、引数の位置を指定したい場合は、引数を埋め込む位置を`$`で指定できます。
引数が複数ある場合は、`$0`、`$1`と、`$`の後に0から始まる引数のインデックスを記述します。
```
undef inv: R->R latex "$^{-1}"
```

## 公理の宣言
`axiom 変数宣言 { 命題 }`によって公理を宣言できます。
公理には簡略性の命題、同値の命題、含意の命題の3種類を宣言できます。種類によって、推論における使い方が異なります。

### 簡略性の命題
左辺と右辺は等しく、なおかつ、左辺よりも右辺が簡単であることを示します。
```
axiom (A: Prop) { A & True >>= A }
axiom (A: Prop) { A | True >>= True }
```

### 同値の命題
左辺と右辺の簡単さは同じであるときに、左辺と右辺が等しいことを示します。
この種類の命題は、交換律と結合律のみが使用できます。
```
axiom (a, b: N) 	{ a + b = b + a }
axiom (a, b, c: N) 	{ a + (b + c) = (a + b) + c }
axiom (a, b: N) 	{ a * b = b * a }
axiom (a, b, c: N) 	{ a * (b * c) = (a * b) * c }
```
### 含意の命題
左辺から右辺が導出できることを示します。
```
axiom (A: Prop, B: Prop) { A & B => A }
```

## 定義
`def 識別子 変数宣言: 型 { 定義内容 }`によって関数を定義できます。
```
def operator => (A, B: Prop): Prop {
    A | ~B 
}
```