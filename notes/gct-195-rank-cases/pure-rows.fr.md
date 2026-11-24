# L-gct-195 · Obstruction sur les lignes pures

Soit $L$ un espace satisfaisant les quatre équations du desk. Écrivons
$r=(3,3,3,-1)$ et $U_i=\{y:e_i\otimes y\in L\}$, avec $y\in\mathbb C^6$.
Si le noyau du contraste contient une matrice non nulle $A=r\otimes f$,
**au plus un des quatre espaces $U_i$ a dimension au moins deux**.
Le vecteur $f$ est quelconque. En particulier, ce critère s'applique à tout
contre-exemple de rang huit. L'argument ci-dessous est mathématique. Le script
voisin contrôle ses coefficients en arithmétique exacte.

## Équations mixtes

Posons $p_d=\sum_j f_j^d$, avec $p_0=6$. Le calcul sur le profil fixe
donne $p_1=p_2=p_4=0$. On peut aussi le lire directement sur $A$ :
la somme des sous-permanents d'ordre $k$ est $k! e_k(r)e_k(f)$, où
$e_k$ est la fonction symétrique élémentaire. Pour $k=1,2,4$,
$e_k(r)$ est non nul. Les identités de Newton donnent les trois moments annoncés.

Pour $y\in U_i$, le coefficient de $t$ dans l'équation d'ordre $k+1$
sur $A+t(e_i\otimes y)$ est

    k! e_k(r sans i) Σ_j y_j e_k(f sans j),    0 ≤ k ≤ 3.

Les quatre facteurs sont non nuls pour chaque choix de ligne. La récurrence
$e_k(f\text{ sans }j)= e_k(f)-f_j e_{k-1}(f\text{ sans }j)$
donne, successivement, $\sum_j y_j f_j^d=0$ pour $d=0,1,2,3$.
Ainsi $U_i\subseteq C=V^\perp$, où $V$ est engendré par
$1,f,f^2,f^3$ et les puissances s'entendent coordonnée par coordonnée.
On emploie la forme bilinéaire complexe $x\cdot y=\sum_j x_jy_j$.
Pour deux lignes distinctes, l'équation quadratique mixte donne
$U_i\perp U_j$, car les deux vecteurs de ligne ont somme nulle.

## Nombre de valeurs distinctes de f

Le vecteur non nul $f$ prend au moins trois valeurs. Pour une valeur,
$p_1=0$ suffit à exclure le cas. Pour deux valeurs $a,b$ de multiplicités
$m,n>0$, les égalités $ma+nb=ma^2+nb^2=0$ imposent $a=b=0$.

S'il prend trois valeurs, l'interpolation montre que $V$ est l'espace des
fonctions constantes sur chaque classe de valeurs. Alors $C$ a dimension
trois et la forme sur $C$ est non dégénérée. En effet, sur chaque classe,
l'espace de somme nulle est un supplémentaire orthogonal de la droite des
constantes. Deux sous-espaces de dimension deux dans $C$ ne peuvent donc
être orthogonaux.

À partir de quatre valeurs, Vandermonde donne $\dim V=4$ et $\dim C=2$.
Si deux lignes avaient dimension au moins deux, on aurait $U_i=U_j=C$,
et $C$ serait totalement isotrope. Cela entraînerait $C\subseteq V$;
le radical de la forme sur $V$ aurait dimension deux. La matrice de Gram
$(p_{a+b})_{0\le a,b\le3}$ serait de rang au plus deux.
Le mineur principal d'indices $0,1,2$ vaut $-6p_3^2$. On en déduit
$p_3=0$. Le mineur principal $0,2,3$ vaut alors $-6p_5^2$.
Ainsi $p_1,\ldots,p_5$ s'annulent. Par Newton, le polynôme
de racines $f_j$ vaut $X^6-c$, avec $c\ne0$ puisque $f\ne0$.

Dans cette dernière configuration, $f^2\in C$. L'espace $L$ contiendrait
donc $A,Y=e_i\otimes f^2,Z=e_j\otimes f^2$. Dans le quartique
pris sur $sA+tY+uZ$, le coefficient de $s^2tu$ est

    −36 c r_a r_b,    {a,b} = les deux autres lignes.

En effet, dans la somme injective sur quatre colonnes, les exposants sont
$1,1,2,2$. Par inclusion-exclusion sur les partitions, tous les termes
s'annulent sauf celui où les quatre indices coïncident, de coefficient
$(-1)^3 3!\,p_6=-36c$. Ce nombre est non nul, en contradiction avec
l'équation du desk. Cela termine la preuve du critère.

## Faisabilité et portée

L'hypothèse d'un triple canonique ne découle pas des quatre équations sur
une direction. Prendre pour $f$ les cinq racines cinquièmes de l'unité
et zéro. Les quatre premières fonctions symétriques élémentaires s'annulent,
donc $r\otimes f$ engendre une droite de niveau. Aucune paire d'entrées
non nulles n'a pour rapport une racine cubique primitive. Ce témoin teste la
normalisation sur une droite. Il ne construit pas un espace de rang huit.

Le critère ne donne pas de borne sur la dimension du quotient de $L$ par la somme
des quatre espaces de matrices à une seule ligne. Ce quotient peut encore
porter les directions manquantes pour atteindre la dimension neuf.
Pour la borne générale, il faut aussi exclure un espace de dimension neuf
sur lequel le contraste est injectif.

Exécuter `python check_pure_rows.py` pour contrôler les seize identités
polynomiales mixtes, les six coefficients quartiques et le témoin à racines
cinquièmes. Ces calculs sont distincts d'une vérification Lean de L-gct-195.
