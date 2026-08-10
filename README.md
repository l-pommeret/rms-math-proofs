# RMS formal proofs

## À propos (français)

Ce dépôt contient des réponses aux questions sans réponse de la rubrique QR de la
*Revue de la filière Mathématiques*, avec leur formalisation en Lean 4 : <https://www.rms-math.com/rms/upload/Qsansreponse260405.pdf>

Tout y a été produit par une *pipeline* machine : les solutions par un modèle de
langue (GPT-5.6 Sol), les formalisations par *Aristotle*. Le tout a pris moins d'une journée.

Ce chiffre est la seule chose vraiment nouvelle ici : produire des preuves mathématiques est devenu bon marché. Une preuve acceptée par
le noyau Lean garantit que l'énoncé *formalisé* est correct.

Une (petite) partie des réponses retrouve des résultats connus :
Q730 est une redémonstration de la classification de Weyl–Horn, Q804 recoupe des résultats
classiques sur le problème de Tammes.

Signalements bienvenus : erreur mathématique, énoncé formalisé infidèle à la question, ou
question déjà close par une réponse publiée dans la revue.

---

## About (English)

Lean 4 formalizations of answers to open questions from the QR column of the *Revue de la
filière Mathématiques*.

Everything here is machine-generated: solutions by a language model, formalizations by
Aristotle. 

## Status

| Question | Verdict | Couverture Lean |
|---|---|---|
| Q565 | A — complete | complète |
| Q587 | A — complete | complète |
| Q604 | A — complete | complète |
| Q655 | A — complete | complète |
| Q668 | **C — substantial progress** | **partielle** |
| Q701 | A — complete | complète |
| Q706 | **C — substantial progress** | **partielle** |
| Q728 | A — complete | complète |
| Q730 | A — complete *(Weyl–Horn, résultat classique)* | complète |
| Q748 | **C — substantial progress** | **partielle** |
| Q756 | A — complete | complète |
| Q759 | A — complete | complète |
| Q764 | A — complete | complète |
| Q766 | A — complete | complète |
| Q776 | A — complete | complète |
| Q781 | A — complete | complète |
| Q788 | A — complete | complète |
| Q803 | A — complete | complète |
| Q804 | A — complete *(recoupe Tammes)* | **partielle** |
| Q805 | A — complete | complète |
| Q830 | A — complete | complète |
| Q831 | A — complete | complète |
| Q838 | A — complete | complète |
| Q839 | A — complete | complète |
| Q850 | A — complete | complète |
| Q855 | A — complete | complète |
| Q857 | A — complete | complète |
| Q865 | A — complete | complète |
| Q867 | A — complete | complète |
| Q877 | A — complete | complète |
| Q885 | A — complete | complète |
| Q896 | A — complete | complète |
| Q899 | A — complete | complète |

**Verdict** est l'appréciation informelle de la solution : A := solution complète,
C := progrès substantiel avec une part demandée encore ouverte.
**Couverture Lean** dit si la formalisation couvre l'énoncé imprimé en entier ou seulement
une partie ; le périmètre exact est donné en tête de chaque section du livre.

## Livre intermédiaire

[`publication/main.pdf`](publication/main.pdf) rassemble toutes les réponses dont
l'artefact Lean passe la CI. Chaque section donne son verdict, le périmètre exactement
formalisé, et des liens vers la source Lean et le type-check en ligne.

## Vérification

Tous les fichiers sous `lean/RMS/` sont vérifiés par GitHub Actions, avec les versions de
Lean et de mathlib épinglées dans `lean/lean-toolchain` et `lean/lakefile.toml`. Aucun
`sorry`, aucun axiome ajouté.
