#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "follow_line.h"

#define MAX_LINE_LEN  1024
#define MAX_W         210
#define MAX_H         160
#define VEL_OFF       5
#define VEL_N         11
#define MAX_SPEED     5
#define BOOSTS_START  5
#define BOOST_N       6
#define INF           0x3f3f3f3f
#define HEAP_MAX      2000000
#define MAX_PATH      3000

typedef struct {
    int f;
    int s;
} HeapNode;

static int  map_w, map_h, gas_init;
static char track[MAX_H][MAX_W + 2];

static int         g_arr [MAX_H][MAX_W][VEL_N][VEL_N][BOOST_N];
static signed char par_dx[MAX_H][MAX_W][VEL_N][VEL_N][BOOST_N];
static signed char par_dy[MAX_H][MAX_W][VEL_N][VEL_N][BOOST_N];
static signed char par_db[MAX_H][MAX_W][VEL_N][VEL_N][BOOST_N];
static int         heur  [MAX_H][MAX_W];

static signed char gdir_x[MAX_H][MAX_W];
static signed char gdir_y[MAX_H][MAX_W];

static HeapNode heap_data[HEAP_MAX];
static int      heap_sz = 0;

static signed char plan_ax[MAX_PATH];
static signed char plan_ay[MAX_PATH];
static signed char plan_ab[MAX_PATH];
static int plan_len = 0;
static int plan_idx = 0;

static int cur_vx     = 0;
static int cur_vy     = 0;
static int cur_boosts = BOOSTS_START;
static int gas_level  = 0;

static int pack_state(int x, int y, int vx, int vy, int boosts)
{
    return x | (y << 8) | ((vx + VEL_OFF) << 16) | ((vy + VEL_OFF) << 20) | (boosts << 24);
}

static void unpack_state(int s, int *x, int *y, int *vx, int *vy, int *boosts)
{
    *x      =  s        & 0xFF;
    *y      = (s >>  8) & 0xFF;
    *vx     = ((s >> 16) & 0xF) - VEL_OFF;
    *vy     = ((s >> 20) & 0xF) - VEL_OFF;
    *boosts = (s >> 24) & 0x7;
}

static char tile_at(int x, int y)
{
    if (x < 0 || x >= map_w || y < 0 || y >= map_h) return '.';
    return track[y][x];
}

static int is_passable(int x, int y)
{
    char t = tile_at(x, y);
    return (t == '#' || t == '~' || t == '=' || (t >= '1' && t <= '3'));
}

static int is_finish(int x, int y) { return tile_at(x, y) == '='; }
static int is_sand(int x, int y)   { return tile_at(x, y) == '~'; }

static void heap_push(int f, int s)
{
    HeapNode e, tmp;
    int i, parent;
    if (heap_sz >= HEAP_MAX) return;
    e.f = f; e.s = s;
    i = heap_sz++;
    heap_data[i] = e;
    while (i > 0) {
        parent = (i - 1) / 2;
        if (heap_data[parent].f <= heap_data[i].f) break;
        tmp = heap_data[parent];
        heap_data[parent] = heap_data[i];
        heap_data[i] = tmp;
        i = parent;
    }
}

static HeapNode heap_pop(void)
{
    HeapNode top, tmp;
    int i, left, right, smallest;
    top = heap_data[0];
    heap_data[0] = heap_data[--heap_sz];
    i = 0;
    while (1) {
        left = 2*i + 1;
        right = 2*i + 2;
        smallest = i;
        if (left  < heap_sz && heap_data[left].f  < heap_data[smallest].f) smallest = left;
        if (right < heap_sz && heap_data[right].f < heap_data[smallest].f) smallest = right;
        if (smallest == i) break;
        tmp = heap_data[i];
        heap_data[i] = heap_data[smallest];
        heap_data[smallest] = tmp;
        i = smallest;
    }
    return top;
}

/*
 * Dijkstra multi-source depuis toutes les cases '='.
 * Cout d'arete terrain-aware :
 *   piste normale '#' -> 1
 *   sable        '~' -> 2  (force vitesse 1 => plus de tours, plus de conso)
 *
 * heur[y][x] = borne inferieure admissible du carburant pour aller de (x,y) a '='.
 * Admissibilite : carburant minimum par case = 1 (normale) ou 2 (sable).
 * Dijkstra est strictement meilleur que BFS car il tient compte du terrain.
 *
 * Le gradient gdir pointe vers la case voisine de plus faible cout Dijkstra,
 * ce qui donne la meilleure direction vers la finish selon le terrain reel.
 */
static void compute_heuristic(void)
{
    HeapNode cur;
    int x, y, nx, ny, i, nd, cell, edge_cost;
    int dx[4];
    int dy[4];

    dx[0] = 1; dx[1] = -1; dx[2] = 0; dx[3] = 0;
    dy[0] = 0; dy[1] = 0;  dy[2] = 1; dy[3] = -1;

    for (y = 0; y < map_h; y++) {
        for (x = 0; x < map_w; x++) {
            heur[y][x]  = INF;
            gdir_x[y][x] = 0;
            gdir_y[y][x] = 0;
        }
    }

    heap_sz = 0;
    for (y = 0; y < map_h; y++) {
        for (x = 0; x < map_w; x++) {
            if (is_finish(x, y)) {
                heur[y][x] = 0;
                heap_push(0, y * MAX_W + x);
            }
        }
    }

    while (heap_sz > 0) {
        cur = heap_pop();
        cell = cur.s;
        y = cell / MAX_W;
        x = cell % MAX_W;
        if (cur.f > heur[y][x]) continue;

        for (i = 0; i < 4; i++) {
            nx = x + dx[i];
            ny = y + dy[i];
            if (!is_passable(nx, ny)) continue;
            edge_cost = is_sand(nx, ny) ? 2 : 1;
            nd = heur[y][x] + edge_cost;
            if (nd < heur[ny][nx]) {
                heur[ny][nx] = nd;
                gdir_x[ny][nx] = (signed char)(-dx[i]);
                gdir_y[ny][nx] = (signed char)(-dy[i]);
                heap_push(nd, ny * MAX_W + nx);
            }
        }
    }
}

/*
 * Heuristique dynamique compatible avec g = carburant.
 * On projette la vitesse actuelle sur le gradient Dijkstra pour estimer
 * combien de "carburant de deplacement" on va couvrir ce tour.
 * h_dyn = max(0, h - toward) sans diviser par MAX_SPEED
 * car g et h sont dans la meme unite (carburant), pas en tours.
 *
 * Admissibilite : chaque case coute >= 1 unite de carburant =>
 * h - toward est une borne inferieure valide du carburant futur.
 */
static int heuristic_dyn(int h, int vx, int vy, int x, int y)
{
    int toward;
    if (h <= 0) return 0;
    toward = vx * (int)gdir_x[y][x] + vy * (int)gdir_y[y][x];
    if (toward < 0) toward = 0;
    if (toward > h) toward = h;
    return h - toward;
}

static int path_clear(int x, int y, int nx, int ny)
{
    InfoLine line;
    Pos2Dint p;
    initLine(x, y, nx, ny, &line);
    while (nextPoint(&line, &p, +1) > 0) {
        if (p.x == x && p.y == y) continue;
        if (!is_passable(p.x, p.y)) return 0;
    }
    return 1;
}

static int gas_consume(int dvx, int dvy, int vx, int vy, int in_sand)
{
    int g;
    double v2 = (double)(vx*vx + vy*vy);
    g = dvx*dvx + dvy*dvy + (int)(sqrt(3.0 * v2 / 2.0));
    if (in_sand) g++;
    return -g;
}

/*
 * A* avec g = carburant exact consomme depuis l'etat de depart.
 *
 * Elagage de faisabilite : si ng + heur[ny][nx] > gas_remaining,
 * ce chemin epuisera le carburant avant la finish => on ne l'explore pas.
 * Cela garantit que tout plan trouve est realiste avec le carburant disponible.
 *
 * Sans fuel_weight : A* minimise naturellement le carburant total.
 * Les boosts sont utilises seulement si leur cout en carburant est compense
 * par les gains futurs (moins de tours = moins de carburant de velocite).
 *
 * Relance a chaque tour : le carburant restant change a chaque tour,
 * donc l'elagage evolue et le plan s'adapte en permanence.
 */
static int run_astar(int sx, int sy, int svx, int svy, int sboosts, int gas)
{
    int x, y, vx, vy, boosts;
    int dvx, dvy, nvx, nvy, nx, ny, ng, g, h, f, h_dyn;
    int nboosts, use_boost, step_cost;
    HeapNode cur;

    memset(g_arr, 0x3f, sizeof(g_arr));
    heap_sz = 0;

    h = heur[sy][sx];
    if (h == INF || h > gas) return 0;

    g_arr[sy][sx][svx + VEL_OFF][svy + VEL_OFF][sboosts] = 0;
    heap_push(heuristic_dyn(h, svx, svy, sx, sy), pack_state(sx, sy, svx, svy, sboosts));

    while (heap_sz > 0) {
        cur = heap_pop();
        unpack_state(cur.s, &x, &y, &vx, &vy, &boosts);

        g = g_arr[y][x][vx + VEL_OFF][vy + VEL_OFF][boosts];
        h = heur[y][x];
        h_dyn = heuristic_dyn(h, vx, vy, x, y);

        if (h != INF && cur.f > g + h_dyn) continue;

        if (is_finish(x, y)) {
            int tx = x, ty = y, tvx = vx, tvy = vy, tboosts = boosts;
            int lo, hi;
            signed char ta;
            plan_len = 0;

            while (tx != sx || ty != sy || tvx != svx || tvy != svy || tboosts != sboosts) {
                int d1      = (int)par_dx[ty][tx][tvx + VEL_OFF][tvy + VEL_OFF][tboosts];
                int d2      = (int)par_dy[ty][tx][tvx + VEL_OFF][tvy + VEL_OFF][tboosts];
                int db      = (int)par_db[ty][tx][tvx + VEL_OFF][tvy + VEL_OFF][tboosts];
                int pvx     = tvx - d1;
                int pvy     = tvy - d2;
                int px      = tx - tvx;
                int py      = ty - tvy;
                int pboosts = tboosts + db;
                if (plan_len >= MAX_PATH) break;
                plan_ax[plan_len] = (signed char)d1;
                plan_ay[plan_len] = (signed char)d2;
                plan_ab[plan_len] = (signed char)db;
                plan_len++;
                tx = px; ty = py; tvx = pvx; tvy = pvy; tboosts = pboosts;
            }

            lo = 0; hi = plan_len - 1;
            while (lo < hi) {
                ta = plan_ax[lo]; plan_ax[lo] = plan_ax[hi]; plan_ax[hi] = ta;
                ta = plan_ay[lo]; plan_ay[lo] = plan_ay[hi]; plan_ay[hi] = ta;
                ta = plan_ab[lo]; plan_ab[lo] = plan_ab[hi]; plan_ab[hi] = ta;
                lo++; hi--;
            }
            plan_idx = 0;
            return 1;
        }

        for (dvx = -2; dvx <= 2; dvx++) {
            for (dvy = -2; dvy <= 2; dvy++) {
                use_boost = (dvx < -1 || dvx > 1 || dvy < -1 || dvy > 1);
                if (use_boost && boosts <= 0) continue;

                nvx = vx + dvx;
                nvy = vy + dvy;

                if (nvx < -MAX_SPEED || nvx > MAX_SPEED) continue;
                if (nvy < -MAX_SPEED || nvy > MAX_SPEED) continue;
                if (nvx*nvx + nvy*nvy > 25) continue;

                nx = x + nvx;
                ny = y + nvy;

                if (!is_passable(nx, ny)) continue;
                if (is_sand(nx, ny) && nvx*nvx + nvy*nvy > 1) continue;
                if (!path_clear(x, y, nx, ny)) continue;

                h = heur[ny][nx];
                if (h == INF) continue;

                /* Carburant exact consomme par ce mouvement.
                 * vx,vy = vitesse AVANT acceleration (comme dans gas_consume). */
                step_cost = dvx*dvx + dvy*dvy
                          + (int)(sqrt(3.0 * (double)(vx*vx + vy*vy) / 2.0))
                          + (is_sand(x, y) ? 1 : 0);
                ng = g + step_cost;

                /* Elagage : impossible de finir avec le carburant restant. */
                if (ng + h > gas) continue;

                nboosts = boosts - (use_boost ? 1 : 0);

                if (ng < g_arr[ny][nx][nvx + VEL_OFF][nvy + VEL_OFF][nboosts]) {
                    g_arr[ny][nx][nvx + VEL_OFF][nvy + VEL_OFF][nboosts] = ng;
                    par_dx[ny][nx][nvx + VEL_OFF][nvy + VEL_OFF][nboosts] = (signed char)dvx;
                    par_dy[ny][nx][nvx + VEL_OFF][nvy + VEL_OFF][nboosts] = (signed char)dvy;
                    par_db[ny][nx][nvx + VEL_OFF][nvy + VEL_OFF][nboosts] = (signed char)use_boost;
                    f = ng + heuristic_dyn(h, nvx, nvy, nx, ny);
                    heap_push(f, pack_state(nx, ny, nvx, nvy, nboosts));
                }
            }
        }
    }
    return 0;
}

int main(void)
{
    char line_buf[MAX_LINE_LEN];
    int row, len;
    int my_x, my_y, oa_x, oa_y, ob_x, ob_y;
    int exp_x, exp_y;
    int dvx, dvy;
    int initialized;

    exp_x = -1; exp_y = -1;
    initialized = 0;

    if (!fgets(line_buf, MAX_LINE_LEN, stdin)) return EXIT_FAILURE;
    sscanf(line_buf, "%d %d %d", &map_w, &map_h, &gas_init);
    gas_level = gas_init;

    for (row = 0; row < map_h; row++) {
        if (!fgets(line_buf, MAX_LINE_LEN, stdin)) break;
        len = (int)strlen(line_buf);
        while (len > 0 && (line_buf[len-1] == '\n' || line_buf[len-1] == '\r'))
            line_buf[--len] = '\0';
        strncpy(track[row], line_buf, MAX_W);
        track[row][MAX_W] = '\0';
    }

    compute_heuristic();

    while (fgets(line_buf, MAX_LINE_LEN, stdin)) {
        int blocked;

        if (sscanf(line_buf, "%d %d %d %d %d %d",
                   &my_x, &my_y, &oa_x, &oa_y, &ob_x, &ob_y) != 6) continue;
        (void)oa_x; (void)oa_y; (void)ob_x; (void)ob_y;

        blocked = (initialized && (my_x != exp_x || my_y != exp_y));
        if (blocked) {
            cur_vx = 0; cur_vy = 0;
            plan_len = 0; plan_idx = 0;
        }

        /* Relance A* a chaque tour : gas_level change a chaque tour,
         * donc l'elagage de faisabilite evolue et le plan s'adapte. */
        run_astar(my_x, my_y, cur_vx, cur_vy, cur_boosts, gas_level);
        initialized = 1;

        if (gas_level <= 0 || plan_idx >= plan_len) {
            dvx = 0; dvy = 0;
        } else {
            dvx = (int)plan_ax[plan_idx];
            dvy = (int)plan_ay[plan_idx];
            cur_boosts -= (int)plan_ab[plan_idx];
            plan_idx++;
        }

        gas_level += gas_consume(dvx, dvy, cur_vx, cur_vy, is_sand(my_x, my_y));
        cur_vx += dvx;
        cur_vy += dvy;
        exp_x = my_x + cur_vx;
        exp_y = my_y + cur_vy;

        fprintf(stdout, "%d %d", dvx, dvy);
        fflush(stdout);
    }

    return EXIT_SUCCESS;
}
