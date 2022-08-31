# Juna
```
       _
      | |
      | |_   _ _ __   __ _
  _   | | | | | '_ \ / _` |
 | |__| | |_| | | | | (_| |
  \____/ \__,_|_| |_|\__,_|
```
Juna is a school project that I wrote for my lambda calculus class (taught
by Didier Rémy, François Pottier and Yann Régis-Gianas) for my masters, in 2018.

Juna is a compiler for a call-by-value lambda calculus with a type system that
supports Hindley-Milner style prenex polymorphism, as well as GADTs. Juna is
supposed to have full type inference, based on the "wobbly types" algorithm of
Simon Peyton Jones et al.

Another interesting point about Juna is that it is compiled to C in continuation
passing style (a CPS translation is applied before compilation) with a
defunctionalization pass.

The language is not quite polished: it lacks important features such as deep
pattern matching, mutual recursion, pattern exhaustivity checks, and it has no
garbage collection (which means no memory managment features at all: an
infinite loop will quickly fill your memory).

Juna is mostly a sandbox for cool PL concepts that I tried to understand at the
time, and is not intented for actual use. However, it does work: the folder
"tests" contains a handful of demonstration programs, including a merge sort
and some demonstration of GADT capabilities.

I now attach the original README (in French) that I wrote at the time:

-------

Un programme est constitué d'un seul fichier (pour le moment), qui
comporte une suite de déclarations de type puis un terme.
```
typedecl ::=
| 'type' family = intro | ... | intro 'end'

intro ::=
| cons : type

term ::=
| var
| cons
| term op term
| (term, term)
| 'fun' var -> term
| term term
| 'match' term 'with' clause | ... | clause 'end'
| 'let' var = term 'in' term
| 'let' var : typescheme = term 'in' term

clause ::=
| pattern => term

pattern ::=
| _
| var
| cons var ... var

typescheme ::=
| 'forall' typevar ... typevar, type

type ::=
| typevar
| type * type
| family type ... type
| type -> type
```
Les fonctions prédéfinies sont : print_int, print_string, fst, snd
Les types prédéfinis sont : string, int, unit, bool
Les constructeurs prédéfinis sont : True, False, Unit




Pour le système de typage, j'ai tout d'abord implanté un vérificateur qui génère
des contraintes et les résout par congruence closure (respectivement
TypeChecking.ml et UnionFind.ml). J'ai envisagé de m'en servir pour l'inférence,
mais je ne savais pas trop comment m'y prendre sans demander des annotations
systématiques à chaque utilisation de GADTs. Du coup, j'ai préféré implanter
les "Wobbly types" d'après [Jones et al, simple unification based type inference
for GADTs]. J'ai mis un certain temps (de l'ordre de la semaine) à comprendre
les détails... Ma version est dans TypeInference.ml

Moralement, la première version devrait pouvoir servir à vérifier l'inférence,
parce qu'elle est bien plus compréhensible. Dans les faits, je suis trop juste
sur les délais pour me permettre de la débuger, donc elle est juste là pour
décorer.

Le pattern matching est seulement superficiel pour l'instant. J'aurais voulu
faire mieux... Son implantation est répartie dans un peu tous les fichiers,
étant donné que chaque étape doit le prendre en compte.

J'ai ajouté quelques opérateurs de comparaison d'entiers (<, >, <=, >=, =).

J'ai également ajouté une version sommaire des chaînes de caractères, juste le
minimum requis pour pouvoir utiliser print_string.

Les commentaires sont présents ou non selon mon humeur au moment où j'ai écrit
le morceau de code correspondant.




Comme le résultat n'a plus grand chose à voir avec le langage original, j'ai
remplacé entièrement le dossier de tests. Il contient

- arithmetic.juna : Opérations entières et comparaisons
- bool.juna : Opérations sur les booléens implantées avec les types algébriques
- gadt.juna : Exemple d'utilisation de GADTs
- hello.juna : Hello, world!
- list.juna : Listes, et implantation d'un tri fusion. Très satisfaisant !
- pattern.juna : pattern matching basique
- recursion.juna : boucle infinie (pas très infinie avec GCC)
- polymorphism.juna : fonction polymorphe, avec annotation de type

Et également un dossier fail/, qui montre que mon typeur est un minimum sérieux.
Et qu'il affiche des erreurs plus ou moins informatives et compréhensibles.
Le fichier le plus intéressant dans ce dossier est gadt.juna, auquel j'ai retiré
l'annotation de type : cela empêche la spécialisation des types.




Sont implantés à moitié, par manque de temps :

- Wildcard "_" pour le pattern matching
- Annotations pour le pattern matching (sont implantées dans le typeur, mais pas
  dans le parseur ?!)
- Structures de données récursives (il manque juste la partie CPS)
- Paires (manque fst et snd)
  à noter qu'on peut les imiter avec un GADT...
- Commentaires intelligents et informatifs

Ne sont pas implantés (et devraient l'être) :

- Sucres syntaxiques. C'est sympa 2 minutes les match pour les booléens
- Pattern matching en profondeur
- Vérification au moins approximative de l'exhaustivité des patterns
- Appel intelligent des fonctions à plusieurs variables
- Fonction mutuellement récursives
- Élimination des rédex administratifs
- Glaneur de cellules/Ramasse-miettes



La structure du code est la suivante :
```
        Lexer + Parser             TypeDeclChecking
  Juna ---------------> RawLambda -----------------> TypeDeclLambda -----
                                                                        |
                                                                        |
  C <-------- Top <-------- Tail <--------- TypeLambda <-----------------
      Finish        Defun            CPS                  TypeInference
```
- Lexer : très peu modifié, quelques lexèmes + chaînes de caractères rajoutés.
- Parser : assez lourdement modifié, pour l'adapter à la syntaxe de Juna.
  J'ai gardé la structure, en rajoutant au fur et à mesure. C'est pas très joli.
- TypeDeclChecking : Nouveau. Vérifie et récupère les déclarations de types et
  les règles d'introduction correspondantes
- TypeInference : Nouveau. Implémentation des Wobbly Types de Jones, avec MGU
  pour l'unification. L'algo de l'article a été légèrement adapté pour ajouter
  des bricoles (types prédéfinis, paires, récursion) et en enlever. Le fichier
  est divisé en plusieurs sections, et aurait gagné à être divisé en plusieurs
  fichiers.
- CPS : Essentiellement le travail attendu. Le langage Tail a été un peu modifié
  pour ajouter les constructeurs de types et le pattern matching (ainsi que les
  opérateurs de comparaison, et print_string). J'ai modifié la définition de la
  récursion dans l'idée de pouvoir faire mes types récursifs, mais j'ai pas eu
  le temps.
- Defun : Essentiellement le travail attendu. Là encore, le langage Top a été
  adapté à ma vision des choses.
- Finish : à peine touché. De quoi gérer les types algébriques, les chaînes de
  caractères et une version pas très claire de la récursion.
- Error.ml : modifié de bric et de broc. Je comprenais pas les formats alors
  j'ai utilisé des string.
- prologue.h : deux macros copiées-collées et adaptées.


Divers :
- TypeChecking : ne compile probablement pas, aurait du servir à la vérification
  des types inférés.
- UnionFind : implante congruence closure. Est censé servir à TypeChecking.
- PatternAnalysis : doux rêve.
