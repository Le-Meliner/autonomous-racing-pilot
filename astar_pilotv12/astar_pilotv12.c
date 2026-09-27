/* ======================================================================
 * astar_pilotv12.c  —  Pilote automatique pour le Grand Prix 2024
 *
 * Ce programme reçoit la carte d'une piste de course et la position
 * de la voiture à chaque tour, puis décide de l'accélération à appliquer
 * pour arriver à l'arrivée le plus vite possible sans tomber en panne
 * d'essence.  L'algorithme utilisé est A* (A-étoile), un algorithme
 * classique de recherche du plus court chemin.
 * ====================================================================== */

#include <stdio.h>    /* Bibliothèque standard pour lire/écrire (printf, scanf, fgets…) */
#include <stdlib.h>   /* Bibliothèque standard pour EXIT_SUCCESS, EXIT_FAILURE, etc.   */
#include <string.h>   /* Bibliothèque pour manipuler les chaînes de caractères (strcpy, strlen…) */
#include <math.h>     /* Bibliothèque mathématique (sqrt = racine carrée, etc.)         */
#include "follow_line.h" /* Fichier local qui fournit les fonctions de tracé de segments (initLine, nextPoint) */

/* ── Constantes globales ────────────────────────────────────────────── */
#define MAX_LINE_LEN  1024   /* Longueur maximale d'une ligne lue depuis l'entrée standard */
#define MAX_W         210    /* Largeur maximale de la carte (en cases)                    */
#define MAX_H         160    /* Hauteur maximale de la carte (en cases)                    */
#define VEL_OFF       5      /* Décalage de vitesse : les vitesses vont de -5 à +5,
                                on les stocke décalées de +5 pour avoir des indices 0..10  */
#define VEL_N         11     /* Nombre de valeurs de vitesse possibles : -5,-4,…,0,…,4,5 = 11 valeurs */
#define MAX_SPEED     5      /* Vitesse maximale autorisée dans chaque direction (absolue)  */
#define INF           0x3f3f3f3f  /* Valeur "infinie" utilisée pour initialiser les distances inconnues */
#define HEAP_MAX      2000000     /* Taille maximale du tas (file de priorité) utilisé par A*            */
#define MAX_PATH      3000        /* Longueur maximale du chemin mémorisé (en nombre de pas)             */
#define GAS_BUFFER    10          /* Réserve de carburant à garder en permanence (marge de sécurité)     */

/*
 * FUEL_DIV : diviseur de la penalite carburant dans g.
 * g = 1 + step_fuel / FUEL_DIV par etat.
 *   FUEL_DIV grand -> proche de pure minimisation tours (comme v1, rapide mais peut manquer de gaz)
 *   FUEL_DIV petit -> proche de minimisation carburant (comme v10, finit toujours mais lent)
 *   FUEL_DIV=4 : a vitesse 5, step_fuel~6, penalite ~1.5/tour => compromis vitesse/economie.
 * L'elagage de faisabilite (fuel_g) garantit qu'on ne tombe jamais en panne.
 */
/* FUEL_DIV contrôle l'équilibre entre vitesse et économie d'essence.
   Plus il est grand, plus le pilote va vite (mais risque la panne).
   Plus il est petit, plus il économise (mais va moins vite).          */
#define FUEL_DIV      2

/* ── Structure d'un nœud dans le tas (file de priorité min) ─────────── */
typedef struct {
    int f;  /* Valeur de priorité f = g + h (coût déjà parcouru + estimation restante) */
    int s;  /* État encodé en un seul entier : position + vitesse (voir pack_state)     */
} HeapNode;

/* ── Variables globales (accessibles partout dans le fichier) ───────── */
static int  map_w, map_h, gas_init; /* Largeur, hauteur de la carte, et carburant initial */
static char track[MAX_H][MAX_W + 2]; /* La carte de la piste, stockée ligne par ligne       */

/* Tableaux 4D : une valeur par case (x,y) et par couple de vitesses (vx,vy) */
static int         g_arr [MAX_H][MAX_W][VEL_N][VEL_N]; /* Coût minimal trouvé jusqu'à chaque état   */
static int         fuel_g[MAX_H][MAX_W][VEL_N][VEL_N]; /* Carburant réel consommé jusqu'à chaque état */
static signed char par_dx[MAX_H][MAX_W][VEL_N][VEL_N]; /* Accélération x du parent (pour reconstruire le chemin) */
static signed char par_dy[MAX_H][MAX_W][VEL_N][VEL_N]; /* Accélération y du parent (pour reconstruire le chemin) */
static int         heur  [MAX_H][MAX_W];  /* Heuristique : distance estimée à l'arrivée depuis chaque case */
static signed char gdir_x[MAX_H][MAX_W]; /* Direction x vers l'arrivée (calculée par Dijkstra)            */
static signed char gdir_y[MAX_H][MAX_W]; /* Direction y vers l'arrivée (calculée par Dijkstra)            */

/* ── Tas binaire (min-heap) ─────────────────────────────────────────── */
static HeapNode heap_data[HEAP_MAX]; /* Tableau qui stocke les nœuds du tas          */
static int      heap_sz = 0;         /* Nombre d'éléments actuellement dans le tas   */

/* ── Chemin planifié ─────────────────────────────────────────────────── */
static signed char plan_ax[MAX_PATH]; /* Séquence d'accélérations x à effectuer      */
static signed char plan_ay[MAX_PATH]; /* Séquence d'accélérations y à effectuer      */
static int plan_len = 0;              /* Nombre de pas dans le chemin planifié        */

/* ── État courant de la voiture ──────────────────────────────────────── */
static int cur_vx    = 0; /* Vitesse courante en x (horizontal)           */
static int cur_vy    = 0; /* Vitesse courante en y (vertical)             */
static int gas_level = 0; /* Niveau de carburant restant                  */

/* ======================================================================
 * pack_state : encode (x, y, vx, vy) en un seul entier pour le stocker
 *              efficacement dans le tas.
 *
 * On place chaque valeur dans une "tranche" de bits différente :
 *   bits  0..7  → x  (position horizontale)
 *   bits  8..15 → y  (position verticale)
 *   bits 16..19 → vx + VEL_OFF  (vitesse x décalée, toujours positive)
 *   bits 20..23 → vy + VEL_OFF  (vitesse y décalée, toujours positive)
 * ====================================================================== */
static int pack_state(int x, int y, int vx, int vy)
{
    return x | (y << 8) | ((vx + VEL_OFF) << 16) | ((vy + VEL_OFF) << 20);
    /* '|'  = OU binaire (combine des bits)
       '<<' = décalage à gauche (multiplie par une puissance de 2)   */
}

/* ======================================================================
 * unpack_state : décode l'entier 's' pour retrouver x, y, vx, vy.
 *                C'est l'opération inverse de pack_state.
 * ====================================================================== */
static void unpack_state(int s, int *x, int *y, int *vx, int *vy)
{
    *x  =  s        & 0xFF;         /* Garde seulement les 8 bits du bas (masque 0xFF = 11111111 en binaire) */
    *y  = (s >>  8) & 0xFF;         /* Décale de 8 bits à droite puis masque → récupère y                   */
    *vx = ((s >> 16) & 0xF) - VEL_OFF; /* Décale de 16 bits, masque sur 4 bits (0xF), puis retire le décalage */
    *vy = ((s >> 20) & 0xF) - VEL_OFF; /* Idem pour vy, décalé de 20 bits                                     */
}

/* ======================================================================
 * tile_at : retourne le caractère de la case (x, y) sur la carte.
 *           Si (x, y) est hors de la carte, retourne '.' (hors-piste).
 * ====================================================================== */
static char tile_at(int x, int y)
{
    if (x < 0 || x >= map_w || y < 0 || y >= map_h) return '.'; /* Hors limites → hors piste */
    return track[y][x]; /* Retourne le caractère stocké dans le tableau de la carte */
}

/* ======================================================================
 * is_passable : renvoie 1 si la case (x,y) est praticable, 0 sinon.
 * Légende de la carte :
 *   '#'       = piste normale (bitume)
 *   '~'       = sable (ralentit et consomme plus)
 *   '='       = ligne d'arrivée
 *   '1','2','3' = zones spéciales (ravitaillement ?)
 *   '.'       = mur ou hors-piste (interdit)
 * ====================================================================== */
static int is_passable(int x, int y)
{
    char t = tile_at(x, y);                                          /* Récupère le type de la case */
    return (t == '#' || t == '~' || t == '=' || (t >= '1' && t <= '3')); /* 1 si praticable, 0 sinon  */
}

/* Fonctions utilitaires : teste si une case est l'arrivée ou du sable */
static int is_finish(int x, int y) { return tile_at(x, y) == '='; } /* '=' = ligne d'arrivée */
static int is_sand(int x, int y)   { return tile_at(x, y) == '~'; } /* '~' = sable           */

/* ======================================================================
 * heap_push : ajoute un nœud (f, s) dans le tas min.
 *
 * Un tas min est une structure qui garde toujours le plus petit élément
 * en haut.  On l'utilise ici pour traiter en priorité les états avec
 * la plus petite valeur f = g + h (principe de A*).
 *
 * Après insertion en bas, on "remonte" le nœud tant qu'il est plus petit
 * que son parent (opération appelée "sift-up" ou "percolation").
 * ====================================================================== */
static void heap_push(int f, int s)
{
    HeapNode e, tmp;   /* Variables temporaires pour manipuler les nœuds */
    int i, parent;     /* Index courant et index du parent dans le tableau */
    if (heap_sz >= HEAP_MAX) return; /* Tas plein : on abandonne (ne devrait pas arriver) */
    e.f = f; e.s = s;                /* Crée le nouveau nœud avec sa priorité et son état  */
    i = heap_sz++;                   /* Place le nœud à la fin du tableau, puis incrémente la taille */
    heap_data[i] = e;                /* Copie le nœud dans le tableau                                */
    while (i > 0) {                  /* Tant qu'on n'est pas à la racine (indice 0)                  */
        parent = (i - 1) / 2;       /* Dans un tas en tableau, le parent de l'indice i est (i-1)/2  */
        if (heap_data[parent].f <= heap_data[i].f) break; /* Si le parent est déjà ≤ enfant, c'est bon */
        tmp = heap_data[parent];     /* Échange le nœud courant et son parent                        */
        heap_data[parent] = heap_data[i];
        heap_data[i] = tmp;
        i = parent;                  /* Continue à remonter depuis la nouvelle position               */
    }
}

/* ======================================================================
 * heap_pop : retire et retourne le nœud de plus petite priorité (racine).
 *
 * On met le dernier élément du tableau à la racine, puis on le
 * "descend" jusqu'à sa place correcte (opération "sift-down").
 * ====================================================================== */
static HeapNode heap_pop(void)
{
    HeapNode top, tmp;            /* 'top' = nœud extrait, 'tmp' sert aux échanges */
    int i, left, right, smallest; /* Indices pour parcourir le tas                 */
    top = heap_data[0];           /* Sauvegarde la racine (minimum) à retourner    */
    heap_data[0] = heap_data[--heap_sz]; /* Déplace le dernier élément à la racine et réduit la taille */
    i = 0;                        /* On repart de la racine                        */
    while (1) {                   /* Boucle infinie : on sort avec 'break'         */
        left  = 2*i + 1;          /* Indice de l'enfant gauche dans le tableau     */
        right = 2*i + 2;          /* Indice de l'enfant droit dans le tableau      */
        smallest = i;             /* On suppose que le nœud courant est le plus petit */
        if (left  < heap_sz && heap_data[left].f  < heap_data[smallest].f) smallest = left;  /* Enfant gauche plus petit ? */
        if (right < heap_sz && heap_data[right].f < heap_data[smallest].f) smallest = right; /* Enfant droit plus petit ?  */
        if (smallest == i) break; /* Le nœud courant est bien le plus petit → on s'arrête */
        tmp = heap_data[i];       /* Échange le nœud courant avec le plus petit de ses enfants */
        heap_data[i] = heap_data[smallest];
        heap_data[smallest] = tmp;
        i = smallest;             /* Continue à descendre                          */
    }
    return top;                   /* Retourne le nœud qui était en racine (le minimum) */
}

/*
 * Dijkstra multi-source depuis '='.
 * Cout terrain : sable=2, piste=1.
 * heur[y][x] = borne inf admissible du carburant pour atteindre '='.
 * gdir[y][x] = direction vers '=' (pour l'heuristique dynamique).
 */
/* ======================================================================
 * compute_heuristic : calcule pour chaque case de la carte la distance
 *   minimale (en coût carburant) jusqu'à la ligne d'arrivée '='.
 *
 * On utilise l'algorithme de Dijkstra "multi-source" : on part de TOUTES
 * les cases '=' en même temps et on propage les distances vers l'extérieur.
 * Résultat stocké dans heur[y][x] et la direction dans gdir_x/gdir_y.
 *
 * Cette heuristique sera utilisée par A* pour estimer le coût restant
 * à partir de n'importe quelle position.
 * ====================================================================== */
static void compute_heuristic(void)
{
    HeapNode cur;                    /* Nœud courant extrait du tas                           */
    int x, y, nx, ny, i, nd, cell, edge_cost; /* Variables de travail pour le Dijkstra       */
    int dx[4]; int dy[4];            /* Les 4 directions : droite, gauche, bas, haut          */

    /* Initialisation des 4 directions cardinales */
    dx[0]=1; dx[1]=-1; dx[2]=0; dx[3]=0;  /* Déplacements en x : +1 (droite), -1 (gauche), 0, 0 */
    dy[0]=0; dy[1]=0;  dy[2]=1; dy[3]=-1; /* Déplacements en y : 0, 0, +1 (bas), -1 (haut)       */

    /* Étape 1 : initialise toutes les cases à "infini" (distance inconnue) */
    for (y = 0; y < map_h; y++)
        for (x = 0; x < map_w; x++) {
            heur[y][x] = INF;        /* Distance infinie : on ne sait pas encore comment y aller */
            gdir_x[y][x] = 0;        /* Direction vers l'arrivée inconnue pour l'instant         */
            gdir_y[y][x] = 0;
        }

    /* Étape 2 : met les cases d'arrivée '=' à distance 0 et les ajoute au tas */
    heap_sz = 0;                     /* Vide le tas avant utilisation                           */
    for (y = 0; y < map_h; y++)
        for (x = 0; x < map_w; x++)
            if (is_finish(x, y)) {   /* Si c'est une case d'arrivée…                            */
                heur[y][x] = 0;      /* …distance 0 : on est déjà à l'arrivée !                 */
                heap_push(0, y * MAX_W + x); /* Ajoute la case au tas avec priorité 0           */
            }

    /* Étape 3 : propagation Dijkstra (on explore depuis les cases les plus proches d'abord) */
    while (heap_sz > 0) {            /* Tant qu'il reste des cases à explorer                   */
        cur = heap_pop();            /* Prend la case avec la plus petite distance               */
        cell = cur.s;                /* 'cell' = y*MAX_W + x (codage de la position en 1D)       */
        y = cell / MAX_W;            /* Retrouve la ligne y                                      */
        x = cell % MAX_W;            /* Retrouve la colonne x                                    */
        if (cur.f > heur[y][x]) continue; /* Si on a déjà trouvé mieux, on ignore ce nœud périmé */
        for (i = 0; i < 4; i++) {   /* Parcourt les 4 voisins (haut, bas, gauche, droite)        */
            nx = x + dx[i];          /* Coordonnée x du voisin                                   */
            ny = y + dy[i];          /* Coordonnée y du voisin                                   */
            if (!is_passable(nx, ny)) continue;          /* Le voisin est un mur → on le saute   */
            edge_cost = is_sand(nx, ny) ? 2 : 1;        /* Sable coûte 2, piste normale coûte 1  */
            nd = heur[y][x] + edge_cost;                 /* Nouvelle distance possible pour (nx,ny) */
            if (nd < heur[ny][nx]) { /* Si on a trouvé un chemin plus court…                    */
                heur[ny][nx] = nd;   /* …met à jour la distance                                  */
                gdir_x[ny][nx] = (signed char)(-dx[i]); /* La direction vers '=' est l'inverse du déplacement */
                gdir_y[ny][nx] = (signed char)(-dy[i]);
                heap_push(nd, ny * MAX_W + nx);          /* Ajoute le voisin au tas pour l'explorer */
            }
        }
    }
}

/*
 * Heuristique dynamique admissible en tours.
 * toward = projection de la vitesse sur la direction vers '='.
 * On soustrait toward de h (carburant terrain restant) avant de diviser par MAX_SPEED.
 * => A* explore en priorite les etats deja lances vers l'arrivee.
 */
/* ======================================================================
 * heuristic_dyn : calcule une estimation (en nombre de tours) du temps
 *   minimum pour aller d'une case à l'arrivée.
 *
 * L'idée : si la voiture va déjà dans la bonne direction, on en profite.
 * 'h'     = distance en coût carburant vers l'arrivée (issue de Dijkstra)
 * 'vx/vy' = vitesse actuelle de la voiture
 * 'toward'= composante de la vitesse dans la direction de l'arrivée
 *           (produit scalaire vitesse × direction_vers_arrivée)
 * On soustrait 'toward' à h pour tenir compte de l'élan déjà acquis,
 * puis on divise par MAX_SPEED (vitesse max) : minimum de tours nécessaires.
 * ====================================================================== */
static int heuristic_dyn(int h, int vx, int vy, int x, int y)
{
    int toward;                      /* Projection de la vitesse vers l'arrivée                 */
    if (h <= 0) return 0;            /* Déjà à l'arrivée (ou après) → 0 tours                  */
    toward = vx * (int)gdir_x[y][x] + vy * (int)gdir_y[y][x]; /* Produit scalaire v · dir_arrivée */
    if (toward < 0) toward = 0;      /* On ne compte pas si on s'éloigne                       */
    if (toward > h) toward = h;      /* L'élan ne peut pas dépasser la distance restante        */
    return (h - toward) / MAX_SPEED; /* Estimation optimiste : on suppose qu'on va à vitesse max */
}

/* ======================================================================
 * path_clear : vérifie que le segment de droite allant de (x,y) à (nx,ny)
 *   ne traverse pas de case impassable.
 *
 * Quand la voiture se déplace d'une case à une autre, sa trajectoire réelle
 * traverse peut-être des cases intermédiaires.  Cette fonction vérifie
 * que toutes ces cases intermédiaires sont praticables (pas de mur).
 * Elle utilise follow_line.h pour énumérer les cases traversées.
 * ====================================================================== */
static int path_clear(int x, int y, int nx, int ny)
{
    InfoLine line;     /* Structure qui décrit le segment à parcourir (issue de follow_line.h) */
    Pos2Dint p;        /* Une case intermédiaire sur le segment                               */
    initLine(x, y, nx, ny, &line);   /* Initialise l'itérateur de segment de (x,y) à (nx,ny) */
    while (nextPoint(&line, &p, +1) > 0) { /* Tant qu'il reste des cases sur le segment…     */
        if (p.x == x && p.y == y) continue; /* Ignore la case de départ                      */
        if (!is_passable(p.x, p.y)) return 0; /* Case impassable trouvée → chemin bloqué      */
    }
    return 1; /* Toutes les cases intermédiaires sont praticables → chemin libre              */
}

/* ======================================================================
 * gas_consume : calcule le carburant CONSOMMÉ lors d'un pas.
 *
 * Formule de consommation :
 *   - dvx²+dvy² : énergie dépensée pour accélérer (freiner = accélération négative)
 *   - sqrt(3/2 * v²) : énergie liée aux frottements à la vitesse (v, vy) avant déplacement
 *   - +1 si le déplacement se fait sur du sable
 *
 * Retourne une valeur NÉGATIVE car c'est de la consommation (on soustrait du carburant).
 * ====================================================================== */
static int gas_consume(int dvx, int dvy, int vx, int vy, int in_sand)
{
    int g;                                         /* Consommation calculée (positive)         */
    double v2 = (double)(vx*vx + vy*vy);           /* Vitesse au carré (v²) avant le pas       */
    g = dvx*dvx + dvy*dvy + (int)(sqrt(3.0 * v2 / 2.0)); /* Consommation = accélération² + frottements */
    if (in_sand) g++;                              /* Surcoût de +1 si on est sur du sable     */
    return -g;                                     /* Retourne la valeur négative (on dépense) */
}

/*
 * A* relance a chaque tour depuis la position courante.
 *
 * g = 1 + step_fuel / FUEL_DIV
 *   Objectif principal : minimiser les tours (+1 par etat).
 *   Penalite douce carburant : step_fuel/FUEL_DIV incite a ne pas gaspiller
 *   sans interdire les vitesses elevees.
 *
 * fuel_g : carburant reel consomme. Sert uniquement a l'elagage :
 *   fuel_g + heur + GAS_BUFFER > gas => chemin infaisable => ignore.
 *   Garantit qu'on finit la course avec GAS_BUFFER unites de reserve.
 *
 * h = heuristic_dyn : borne inf admissible en tours (Dijkstra / MAX_SPEED).
 */
/* ======================================================================
 * run_astar : lance l'algorithme A* depuis la position (sx,sy) avec la
 *   vitesse (svx,svy) et le carburant 'gas'.
 *
 * A* est une version améliorée de Dijkstra : au lieu d'explorer dans
 * toutes les directions, il utilise une heuristique (estimation du coût
 * restant) pour explorer d'abord les chemins les plus prometteurs.
 *
 * L'état ici est : (x, y, vx, vy) = position + vitesse.
 * À chaque état, on essaie les 9 accélérations possibles
 * (dvx, dvy) ∈ {-1,0,+1} × {-1,0,+1}.
 *
 * Quand on atteint une case '=', on remonte le chemin via les tableaux
 * 'par_dx'/'par_dy' (ancêtres) et on stocke le plan dans plan_ax/plan_ay.
 *
 * Retourne 1 si un chemin est trouvé, 0 sinon.
 * ====================================================================== */
static int run_astar(int sx, int sy, int svx, int svy, int gas)
{
    int x, y, vx, vy;                       /* Position et vitesse de l'état courant     */
    int dvx, dvy, nvx, nvy, nx, ny;         /* Accélération et état suivant              */
    int ng, ng_fuel, g, h, f, h_dyn, step_cost; /* Coûts intermédiaires                 */
    HeapNode cur;                            /* Nœud extrait du tas                       */

    /* ── Initialisation ── */
    plan_len = 0;                            /* Efface l'ancien plan                      */
    memset(g_arr,  0x3f, sizeof(g_arr));     /* Remplit g_arr avec "infini" (0x3f3f3f3f)  */
    memset(fuel_g, 0x3f, sizeof(fuel_g));    /* Idem pour le carburant consommé           */
    heap_sz = 0;                             /* Vide le tas                               */

    h = heur[sy][sx];                        /* Distance estimée depuis le point de départ */
    if (h == INF || h + GAS_BUFFER > gas) return 0; /* Arrivée inaccessible ou pas assez de carburant → abandon */

    /* Initialise l'état de départ : coût 0, carburant 0 dépensé */
    g_arr [sy][sx][svx + VEL_OFF][svy + VEL_OFF] = 0;
    fuel_g[sy][sx][svx + VEL_OFF][svy + VEL_OFF] = 0;
    /* Ajoute l'état de départ dans le tas avec la priorité = heuristique seule (g=0) */
    heap_push(heuristic_dyn(h, svx, svy, sx, sy), pack_state(sx, sy, svx, svy));

    /* ── Boucle principale de A* ── */
    while (heap_sz > 0) {                    /* Tant qu'il reste des états à explorer     */
        cur = heap_pop();                    /* Prend l'état le plus prometteur (f min)   */
        unpack_state(cur.s, &x, &y, &vx, &vy); /* Décode la position et la vitesse       */

        g     = g_arr[y][x][vx + VEL_OFF][vy + VEL_OFF]; /* Coût déjà payé pour atteindre cet état */
        h     = heur[y][x];                              /* Distance estimée vers l'arrivée          */
        h_dyn = heuristic_dyn(h, vx, vy, x, y);          /* Estimation dynamique (tient compte de la vitesse) */

        /* Si le nœud est périmé (on a depuis trouvé mieux), on l'ignore */
        if (h != INF && cur.f > g + h_dyn) continue;

        /* ── A-t-on atteint l'arrivée ? ── */
        if (is_finish(x, y)) {
            /* Reconstruction du chemin en remontant les ancêtres */
            int tx = x, ty = y, tvx = vx, tvy = vy; /* Position/vitesse courante pendant la remontée */
            int lo, hi;                /* Bornes pour inverser le tableau                */
            signed char ta;            /* Variable temporaire pour l'échange             */
            plan_len = 0;              /* Remet le compteur de plan à 0                  */

            /* On remonte de l'arrivée jusqu'au départ grâce aux tableaux parents */
            while (tx != sx || ty != sy || tvx != svx || tvy != svy) {
                int d1  = (int)par_dx[ty][tx][tvx + VEL_OFF][tvy + VEL_OFF]; /* Accélération x qui a mené ici */
                int d2  = (int)par_dy[ty][tx][tvx + VEL_OFF][tvy + VEL_OFF]; /* Accélération y qui a mené ici */
                int pvx = tvx - d1;    /* Vitesse x avant ce pas (on retire l'accélération)  */
                int pvy = tvy - d2;    /* Vitesse y avant ce pas                             */
                int px  = tx - tvx;    /* Position x avant ce pas (on retire le déplacement) */
                int py  = ty - tvy;    /* Position y avant ce pas                            */
                if (plan_len >= MAX_PATH) break; /* Sécurité : ne pas dépasser la taille du tableau */
                plan_ax[plan_len] = (signed char)d1; /* Stocke l'accélération x dans le plan  */
                plan_ay[plan_len] = (signed char)d2; /* Stocke l'accélération y dans le plan  */
                plan_len++;            /* Incrémente le nombre de pas                        */
                tx = px; ty = py; tvx = pvx; tvy = pvy; /* Recule d'un pas vers le départ    */
            }

            /* Le tableau plan_ax/plan_ay est dans l'ordre INVERSE (arrivée→départ).
               On l'inverse pour avoir l'ordre correct (départ→arrivée). */
            lo = 0; hi = plan_len - 1; /* Pointeurs au début et à la fin du tableau */
            while (lo < hi) {          /* Tant que les pointeurs ne se croisent pas  */
                ta = plan_ax[lo]; plan_ax[lo] = plan_ax[hi]; plan_ax[hi] = ta; /* Échange en x */
                ta = plan_ay[lo]; plan_ay[lo] = plan_ay[hi]; plan_ay[hi] = ta; /* Échange en y */
                lo++; hi--;            /* Rapproche les pointeurs                   */
            }
            return 1; /* Chemin trouvé ! */
        }

        /* ── Exploration des états voisins ── */
        /* On essaie les 9 combinaisons d'accélération (dvx,dvy) ∈ {-1,0,+1}² */
        for (dvx = -1; dvx <= 1; dvx++) {   /* dvx : accélération en x (-1, 0, ou +1)   */
            for (dvy = -1; dvy <= 1; dvy++) { /* dvy : accélération en y (-1, 0, ou +1) */
                nvx = vx + dvx;              /* Nouvelle vitesse en x après accélération  */
                nvy = vy + dvy;              /* Nouvelle vitesse en y après accélération  */

                /* Vérifie que la vitesse reste dans les limites autorisées */
                if (nvx < -MAX_SPEED || nvx > MAX_SPEED) continue; /* Trop rapide en x → interdit */
                if (nvy < -MAX_SPEED || nvy > MAX_SPEED) continue; /* Trop rapide en y → interdit */
                if (nvx*nvx + nvy*nvy > 25) continue; /* Norme de vitesse² > 5² → interdit (vitesse vecteur max) */

                nx = x + nvx;  /* Nouvelle position x après déplacement (la voiture se déplace à sa nouvelle vitesse) */
                ny = y + nvy;  /* Nouvelle position y après déplacement */

                if (!is_passable(nx, ny)) continue;           /* La destination est un mur → interdit        */
                if (is_sand(nx, ny) && nvx*nvx + nvy*nvy > 1) continue; /* Sur le sable : vitesse max = 1     */
                if (!path_clear(x, y, nx, ny)) continue;     /* Trajectoire bloque un mur → interdit         */

                h = heur[ny][nx];     /* Distance estimée depuis la nouvelle case vers l'arrivée */
                if (h == INF) continue; /* La destination n'a pas de chemin vers l'arrivée → impossible */

                /* Calcule le coût en carburant de ce pas */
                step_cost = dvx*dvx + dvy*dvy                           /* Énergie d'accélération          */
                          + (int)(sqrt(3.0 * (double)(vx*vx + vy*vy) / 2.0)) /* Frottements à vitesse actuelle */
                          + (is_sand(x, y) ? 1 : 0);                   /* Surcoût sable si on est sur le sable */

                ng_fuel = fuel_g[y][x][vx + VEL_OFF][vy + VEL_OFF] + step_cost; /* Carburant total consommé si on emprunte ce chemin */
                if (ng_fuel + h + GAS_BUFFER > gas) continue; /* Pas assez de carburant pour finir → on élimine ce chemin */

                /* Coût composite : minimise le nombre de tours (+1), avec une pénalité douce sur le carburant */
                ng = g + 1 + step_cost / FUEL_DIV;

                /* Si ce chemin est meilleur que le meilleur connu pour cet état (nx,ny,nvx,nvy)… */
                if (ng < g_arr[ny][nx][nvx + VEL_OFF][nvy + VEL_OFF]) {
                    g_arr [ny][nx][nvx + VEL_OFF][nvy + VEL_OFF] = ng;       /* Met à jour le coût       */
                    fuel_g[ny][nx][nvx + VEL_OFF][nvy + VEL_OFF] = ng_fuel;  /* Met à jour le carburant  */
                    par_dx[ny][nx][nvx + VEL_OFF][nvy + VEL_OFF] = (signed char)dvx; /* Mémorise l'accélération x (pour reconstruire le chemin) */
                    par_dy[ny][nx][nvx + VEL_OFF][nvy + VEL_OFF] = (signed char)dvy; /* Mémorise l'accélération y */
                    f = ng + heuristic_dyn(h, nvx, nvy, nx, ny);             /* f = g + h (priorité A*)  */
                    heap_push(f, pack_state(nx, ny, nvx, nvy));               /* Ajoute dans le tas        */
                }
            }
        }
    }
    return 0; /* Aucun chemin trouvé (panne d'essence inévitable ou piste infranchissable) */
}

/* ======================================================================
 * main : point d'entrée du programme.
 *
 * Protocole de communication avec le simulateur (via stdin/stdout) :
 *
 * 1) Le simulateur envoie UNE FOIS au début :
 *    <largeur> <hauteur> <carburant_initial>
 *    puis <hauteur> lignes de texte décrivant la carte.
 *
 * 2) Ensuite, à chaque tour, le simulateur envoie :
 *    <mon_x> <mon_y> <adversaire_A_x> <adversaire_A_y> <adversaire_B_x> <adversaire_B_y>
 *
 * 3) En réponse, le programme écrit sur stdout :
 *    <accélération_x> <accélération_y>
 *    (valeurs entières dans {-1, 0, +1})
 * ====================================================================== */
int main(void)
{
    char line_buf[MAX_LINE_LEN]; /* Tampon pour lire une ligne depuis stdin                */
    int row, len;                /* Compteur de lignes et longueur d'une ligne              */
    int my_x, my_y, oa_x, oa_y, ob_x, ob_y; /* Position de ma voiture et des adversaires A et B */
    int exp_x, exp_y, initialized;           /* Position prévue au tour suivant et drapeau d'init */
    int dvx, dvy;                            /* Accélération décidée pour ce tour              */

    exp_x = -1; exp_y = -1; initialized = 0; /* Pas encore initialisé                          */

    /* ── Lecture de la première ligne : dimensions et carburant ── */
    if (!fgets(line_buf, MAX_LINE_LEN, stdin)) return EXIT_FAILURE; /* Lit la ligne (échec → arrêt) */
    sscanf(line_buf, "%d %d %d", &map_w, &map_h, &gas_init);        /* Extrait largeur, hauteur, carburant */
    gas_level = gas_init;        /* Initialise le niveau de carburant courant                             */

    /* ── Lecture de la carte ligne par ligne ── */
    for (row = 0; row < map_h; row++) {              /* Pour chaque ligne de la carte…              */
        if (!fgets(line_buf, MAX_LINE_LEN, stdin)) break; /* Lit la ligne (arrêt si EOF)            */
        len = (int)strlen(line_buf);                 /* Calcule la longueur de la ligne              */
        while (len > 0 && (line_buf[len-1] == '\n' || line_buf[len-1] == '\r'))
            line_buf[--len] = '\0'; /* Retire les caractères de fin de ligne ('\n', '\r')              */
        strncpy(track[row], line_buf, MAX_W);        /* Copie la ligne dans le tableau de la carte   */
        track[row][MAX_W] = '\0';                    /* S'assure que la chaîne est bien terminée      */
    }

    /* ── Précalcul de l'heuristique (Dijkstra depuis l'arrivée) ── */
    compute_heuristic(); /* Calcule heur[y][x] = distance min en carburant vers '=' depuis (x,y) */

    /* ── Boucle principale : un tour par ligne reçue ── */
    while (fgets(line_buf, MAX_LINE_LEN, stdin)) { /* Lit la position de ce tour                  */
        if (sscanf(line_buf, "%d %d %d %d %d %d",
                   &my_x, &my_y, &oa_x, &oa_y, &ob_x, &ob_y) != 6) continue; /* Ligne invalide → ignore */
        (void)oa_x; (void)oa_y; (void)ob_x; (void)ob_y; /* Les positions des adversaires ne sont pas utilisées
                                                             (void) évite un avertissement du compilateur     */

        /* Détection d'une collision/sortie de piste : si la voiture n'est pas où on l'attendait,
           on suppose que la vitesse a été annulée (remise à zéro) par le simulateur */
        if (initialized && (my_x != exp_x || my_y != exp_y)) {
            cur_vx = 0; cur_vy = 0; /* Réinitialise la vitesse estimée : la voiture s'est arrêtée */
        }
        initialized = 1; /* On a reçu au moins une position : on peut vérifier les suivantes    */

        /* Lance A* depuis la position et vitesse courantes pour planifier le chemin optimal */
        run_astar(my_x, my_y, cur_vx, cur_vy, gas_level);

        /* Choisit l'accélération à appliquer ce tour */
        if (gas_level <= 0 || plan_len == 0) {
            dvx = 0; dvy = 0; /* Pas de carburant ou pas de plan → on ne bouge pas (accélération nulle) */
        } else {
            dvx = (int)plan_ax[0]; /* Prend la première accélération du plan calculé par A* */
            dvy = (int)plan_ay[0];
        }

        /* Met à jour le carburant en soustrayant la consommation de ce pas */
        gas_level += gas_consume(dvx, dvy, cur_vx, cur_vy, is_sand(my_x, my_y));
        /* Note : gas_consume retourne une valeur négative, donc += revient à soustraire */

        /* Met à jour la vitesse estimée (vitesse = ancienne vitesse + accélération) */
        cur_vx += dvx;
        cur_vy += dvy;

        /* Calcule la position prévue AU PROCHAIN TOUR (pour détecter les collisions) */
        exp_x = my_x + cur_vx; /* La voiture va se déplacer de sa nouvelle vitesse */
        exp_y = my_y + cur_vy;

        /* Envoie la décision d'accélération au simulateur */
        fprintf(stdout, "%d %d", dvx, dvy); /* Écrit "dvx dvy" sur la sortie standard */
        fflush(stdout); /* Force l'envoi immédiat (sans attendre que le tampon soit plein) */
    }

    return EXIT_SUCCESS; /* Fin normale du programme */
}
