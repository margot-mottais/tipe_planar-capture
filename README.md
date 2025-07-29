# Jeu des Policiers-et-voleur sur les graphes planaires

Ce dépôt est une archive de mon projet de TIPE réalisé en 2022-2023 en classe préparatoire (CPGE) MP2I-MPI.

## Structure du dépôt 

```
.
├── docs
│   ├── Mcot_23837.pdf
│   └── presentation_23837.pdf
├── LICENSE
├── README.md
└── src
    ├── capture_naif.ml
    ├── capture_pisantechakool-tan.ml
    └── dijkstra.ml
```

Le répertoire `docs` contient les deux documents exigés par l'épreuve commune du TIPE (Travaux d'Initiative Personnelle Encadrés) en CPGE scientifique, à savoir la [diapositive de présentation du projet](/docs/presentation_23837.pdf), ainsi que le rapport de [Mise en Cohérence des Objectifs du TIPE (MCOT)](/docs/Mcot_23837.pdf).

Le répertoire `src` contient le code en OCaml que j'ai produit pour simuler les différentes stratégies de capture du voleur décrites dans les différents papiers que j'ai pu lire, afin de les comparer.
- `capture_naif.ml` réalise les différentes variantes de résolution naive, ainsi que des adaptations à différents cas particuliers de graphes planaires (développées dans la bibliogrpahie). Le programme permet de générer ces graphes spéciaux, comme des grilles ou des arbres aléatoires (dits de Eller).
- `capture_pisantechakool-tan.ml` réalise la solution décrite dans l'article de Pisantechakool et Tan (voir les [références bibliographiques](/docs/Mcot_23837.pdf) en page 3), à savoir la capture à trois policiers sur des graphes planaires. Elle implémente également la génération alétoires de graphes planaires selon plusieurs modèles types (grilles en carrés pleins ou vides, grilles hexagonales).
- `dijkstra.ml` est une implémentation de l'algorithme de Dijkstra par file de priorité, utilisé pour trouver le plus court chemin entre deux sommets dans un graphe. Il était initialement utilisé dans `capture_pisantechakool-tan.ml`, mais a ensuite été remplacé par l'utilisation du module [Queue](https://ocaml.org/manual/5.3/api/Queue.html) de OCaml.