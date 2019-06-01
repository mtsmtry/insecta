# 定理証明言語Insecta
項書き換えを基本とした定理証明言語です。

独自の構文を持った新しい言語です。

プログラムの証明や人間が証明できない難解な定理の証明といったことは目的としておらず、知識を記述する媒体として、自然言語による証明の記述の補助的手段となることを標榜しています。

この言語を用いた、インタラクティブな教科書や数学事典を作ろうと考えています。

似た言語があったら教えてください。(今はイザベルしか知りません)

# 特徴
## インタラクティブなドキュメントを生成できます
API化して、証明を検索したり、自分で定理を簡単に証明できるようなWebサービスを開発する予定です。

## 数式処理システムとして使用できます
定義と命題の宣言をするだけで、ある式をできるだけ簡単な形にするといった数式処理ができます。

項書き換え系によって、定理の宣言を数式処理のアルゴリズムの追加として処理できます。

## 進捗状況
まだできてません。
もうすぐできます。

- [x] 字句解析
- [x] 字句解析エラーメッセージ
- [x] 構文解析
- [ ] 構文解析エラーメッセージ
- [x] 単一化
- [x] 簡略化
- [x] 導出
- [x] 書き換えのマージ
- [ ] 書き換えの書き出し
- [ ] 定義の展開
- [ ] 篩型の展開
- [ ] let文
- [ ] assume文
- [ ] exists抽象化
- [ ] forall具象化
- [ ] 型付け型命題

## マクロ進捗状況
- [ ] 処理系の開発
- [ ] APIの完成
- [ ] Webサービスの開発
- [ ] 杉浦著解析入門Iの形式化
- [ ] Coqのライブラリに相当する程度の証明
- [ ] インタラクティブな教科書の開発

## 簡単に証明ができます
項書き換え系を用いてある程度自動化されているので、式を同値変形するだけで証明できます。

基本的な命令(タクティク)は10種類もありません。

機械的な定理証明独特の仕様に捉われることなく、数学的な証明の本質に集中して証明ができます。

例えば、極限がある数に収束する関数同士の積の極限はその数の積に収束するという定理は、以下のように記述できます。Coqより簡単に証明できます。

- Insectaの場合
```
theorem (a, b: R) (f: Converge(a), g: Converge(b)) {
    n->f[n] * g[n]: Converge(a * b)
proof:
    let M = max(f, g)
    forall eps: R
    target f.Converge(a) & g.Converge(b)
    unfold n >= n_1 -> dist(a, f(n)) < eps/(2*M) & n >= n_2 -> dist(b, g(n)) < eps/(2*abs(a)+1)
    impl assume n >= n_1 & n >= n_2 {
        begin dist(a, f(n)) < eps/(2*M) & dist(b, g(n)) < eps/(2*abs(a)+1)
        impl where dist(a*b, f(n)*g(n)) <= $ {
            begin abs(a*(b-g(n))) + abs(g(n)*(a-f(n)))
            step abs(a)*dist(b, g(n)) + abs(g(n))*dist(a, f(n))
            step eps
        }
    }
    fold goal
}
```
- Coqの場合
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

Isabelleと比較するとこんな感じです。

- Insectaの場合
```
theorem (n: N) {
    n >= 2 => n^2 >= 2*n
proof:
    impl n*n >= 2*n
    step n^2 >= 2*n
}
```

- Isabelleの場合
```
lemma ex':
    fixes n :: nat
    assumes "n ≥ 2"
    shows "2*n ≤ n^2"
using assms
proof (induct n, simp)
    fix n :: nat
    assume a: "2 ≤ n ⟹ 2 * n ≤ n^2" and b: "2 ≤ Suc n"
    have "2 * Suc n ≤ 2 * (n + 1)" using a b by simp
    also have "… ≤ 2 * n + 2" by simp
    also have "… ≤ n^2 + 2 * n + 1" using b by simp
    also have "… = (n+1)^2" using power2_sum [of n 1] by auto
    finally
        show "2 * Suc n ≤ (Suc n)^2" by simp
qed
```

# 文法
## 基本
- ブロック
Pythonのように改行やインデントによって意味が変わることはありません。
セミコロンなども使用しません。
ブロックは、波括弧`{}`によって表現します。

- コメント
`#`から改行までの間はコメントとして認識されます。

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
undef operator +: (N, N)->N 		      latex "+" 
undef operator *: (N, N)->N 		      latex "\cdot"
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
公理には簡略性の命題、同値の命題、含意の命題の3種類を宣言できます。
種類によって、推論における使い方が異なります。

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
axiom (a, b: N) 	  { a + b = b + a }
axiom (a, b, c: N) 	{ a + (b + c) = (a + b) + c }
axiom (a, b: N) 	  { a * b = b * a }
axiom (a, b, c: N) 	{ a * (b * c) = (a * b) * c }
```
交換律や結合律を宣言すると、交換や結合した項が等しいものとして認識されます。

例えば、交換律と結合律を宣言すると、次の項は暗黙的に等しいものと見なされます。
```
a + ((b + c) + d) = (d + b) + (a + c)
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