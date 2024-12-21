```
    ____  _________    ____  __  _________       __  _______ 
   / __ \/ ____/   |  / __ \/  |/  / ____/      /  |/  / __ \
  / /_/ / __/ / /| | / / / / /|_/ / __/        / /|_/ / / / /
 / _, _/ /___/ ___ |/ /_/ / /  / / /____  _   / /  / / /_/ / 
/_/ |_/_____/_/  |_/_____/_/  /_/_____ / (_) /_/  /_/_____/  
```
                                                        

# Projet : Analyseur Syntaxique pour Langage WHILEb
Erwan PONCIN, Maxime BOSSANT, Maxence MAURY

## Contenu des fichiers

### 1. `Project.ml`
Contenu du code du projet OcamL.


### 2. `source_file_coq.v`
Fichier contenant les preuves de `reduction_Pcarre_2`, `SN_SN’` et `SN’_SN` ainsi que les prérequis permettant d'exécuter ces preuves (présents dans le TD 06).

### 3. `anacomb.ml`
Fichier `anacomb.ml` fourni.


---

## Comment Exécuter et Tester le Projet

Pour tester notre projet, il suffit de remplacer `ecrire programme ici` par son programme de test et de changer les états dans mon_state dans le code suivant :

```
let mon_programme = list_of_string "ecrire programme ici";; (* écrire le programme ici *)
let mon_state = [0; 0; 0; 0];; (* écrire l'état de départ du programme ici *)

let (resultat, reste) = b_P mon_programme;;
evalI resultat mon_state;;
```
Quelques petits tests sont également présents à différents emplacement dans le code.
Le projet est sensé s'exécuter correctement.

---

## Questions Traitées et Participants

### Questions Abordées
Toutes les questions de l'énoncé du projet (non faculattives) ont été traitées :

 - **Exercice 1.1.1** (Erwan, Maxime, Maxence)
 - **Exercice 1.1.2** (Erwan, Maxime, Maxence)
 - **Exercice 1.1.3** (Erwan, Maxime, Maxence)
 - **Exercice 1.1.4** (Erwan, Maxime, Maxence)
 - **Exercice 1.2.1** (Erwan, Maxime, Maxence)
 - **Exercice 2.1.1** (Erwan, Maxime, Maxence)
 - **Exercice 2.1.2** (Erwan, Maxime, Maxence)
 - **Exercice 2.1.3** (Erwan, Maxime, Maxence)
 - **Exercice 2.1.4 (facultatif)** (Erwan, Maxime, Maxence)
 - **Exercice 2.2.1** (Erwan, Maxime, Maxence)
 - **Exercice 2.2.2** (Erwan, Maxime, Maxence)
 - **Exercice 2.3.1** (Erwan, Maxime, Maxence)
 - **Exercice 2.3.2** (Erwan, Maxime, Maxence)
 - **Exercice 2.3.3** (Erwan, Maxime, Maxence)
