# Circuits monotones et graphes d’incidence

Les six propositions Lean de cette revue sont des résultats de recherche locaux. Les bornes générales de 25 portes sur Heawood et de 64 portes sur le plan d’ordre trois restent ouvertes.

| Cible étudiée | Résultat vérifié |
|---|---|
| L-meta-3754 | Pour chaque porte d’un circuit AND/OR binaire minimal, tout fil antérieur échoue à au moins un des deux tests de remplacement. Il manque un vrai sur une arête où la porte est vraie, ou il introduit un vrai sur un ensemble indépendant maximal où elle est fausse. Le résultat vaut pour tout graphe simple fini. |
| L-meta-4781 | Une bijection identifie les séparateurs admissibles sur 14 bits aux fonctions monotones sur le cycle résiduel à 8 sommets qui rejettent zéro et acceptent chaque entrée contenant une arête. Une fonction déterminée par quatre coordonnées est un OR sur une classe alternée. |
| L-meta-4051 | Trois lemmes portent sur la sensibilité après fixation de variables, les lectures directes de variables dans un circuit et la possibilité de décoder une fonction d’arête depuis des OR de paires. Le témoin de McGee montre la limite d’un argument par nombre de lectures seul. |
| L-meta-1692 | Un calcul exhaustif sur le plan d’ordre trois identifie les 10 362 entrées négatives forcées et les 28 368 entrées sans incidence individuellement libres. Trois points alignés donnent un contre-exemple à l’exactitude forcée sur toutes les entrées. |

Pour Heawood, le programme dénombre 14 514 289 séparateurs et 919 855 classes sous les seize symétries de l’arête distinguée. Les 58 tests comprennent vingt arêtes obligatoires, 37 ensembles indépendants maximaux et l’arête distinguée. La recherche générale en 24 portes a atteint 180 secondes sans verdict. Les neuf fenêtres testées ont atteint dix-huit secondes chacune. Le générateur utilise la définition `enc2` du projet.

Pour L-meta-3754, sur le chemin à quatre sommets (a,b,c,d), les trois clauses (a ∨  c), (b ∨  d) et (b ∨  c) donnent un circuit de cinq portes en prenant leur conjonction. Le premier AND de ces trois clauses, appliqué aux deux premières, est vrai sur la paire indépendante ({a,d}). Le circuit est au point fixe du relèvement. Il passe les tests de comparaison avec tout fil antérieur. La même fonction se calcule en quatre portes par ((b ∧ (a ∨  c)) ∨ (c ∧  d)). Le test de comparaison seul ne suffit donc pas à conclure L-meta-3754. Les fichiers JSON indiquent les résultats et les délais des recherches SAT sur de petits graphes.

## Reproduction

Compiler Mathlib et le checker du projet avec les versions épinglées. Depuis ce dossier, exécuter `python verify.py <racine-du-checkout>/lean <racine-de-la-toolchain-Lean-4.36.0>`. Les six fichiers de signature sont lus séparément. Le module de dérivation pour L-meta-3754 utilise le module upstream L-meta-2668. La copie du fork est identique au blob `0722c4a5b8473d5ef035bba21f5c4786febb54c5`. [Source de la dépendance upstream](https://github.com/open-goat/pequalnp-proofs/blob/aeef32c907d2bd344ab16172b8baadd5081b0582/lean/PEqualNP/Outside/L_meta_2668.lean).

Les scripts de graphes utilisent Python 3 et NetworkX. Les expériences du plan d’ordre trois utilisent la bibliothèque standard. Les recherches SAT de cette revue ont utilisé le CaDiCaL livré avec Lean 4.36.0 sur Windows. Le protocole des scripts SAT suppose cette installation.

