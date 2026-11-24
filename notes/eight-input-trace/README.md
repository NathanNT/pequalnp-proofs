# Deux preuves d’une même borne de trace

L-meta-4628 interdit à une trace signée sur huit entrées de calculer la fonction d’arête avec onze indices payants. Le module de cette branche donne la preuve de NathanNT par fixation d’une feuille et utilise le certificat à sept entrées de sirusdv, cité dans la source. Le checker du projet a accepté la version publiée sur la signature du desk et revérifié 2 349 constantes.

Le lemme `low255` de dsgallups dans la PR #8718 implique déjà la même borne. Le transport fourni dans ce dossier renomme les sommets selon `[4,0,1,6,7,3,5,2]`, traite les copies et les compléments gratuits et impute chaque opération payante à un indice. Le checker a accepté la même signature et revérifié 2 378 constantes. Cette revue du fork conserve la preuve indépendante et le certificat d’antériorité. [Verdict officiel de #8718](https://github.com/open-goat/pequalnp-proofs/pull/8718#issuecomment-7142528417) et [certificat de sirusdv](https://github.com/open-goat/pequalnp-proofs/pull/6399).

Pour reproduire les contrôles, récupérer la tête publique de #8718 dans un dépôt Git, par exemple avec `git fetch https://github.com/open-goat/pequalnp-proofs.git refs/pull/8718/head`. Exécuter `python verify.py <checkout>/lean <toolchain-Lean-4.36.0> <dépôt-contenant-le-blob-de-8718>` depuis ce dossier. Le script exige le blob exact de dsgallups et construit les trois modules dans un répertoire temporaire.

