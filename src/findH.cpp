#include "tm.hpp"
#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <filesystem>
#include <thread>
#include <mutex>
#include <atomic>
#include <cmath>
#include <fstream>
#include <array>
#include <random>
#include <chrono>
#include <algorithm>
#include <iomanip>

// --- CONFIGURACIÓN DE BÚSQUEDA ---
const int R_TARGET = 3;
const int SAMPLE_SIZE = 2000;       // Cuantas cintas aleatorias probar para calcular el %
const int MAX_STAGNATION = 5000;    // Si no mejora tras X intentos, reinicia (Random Restart)
const int PRINT_INTERVAL_SEC = 300; // 5 minutos (300 segundos)

// Estructuras globales para monitoreo
struct SearchStats {
    std::atomic<double> best_involution_pct;
    std::atomic<double> best_formula_pct;
    std::atomic<unsigned long long> restarts;
    std::atomic<unsigned long long> mutations_tried;
};

SearchStats global_stats{0.0, 0.0, 0, 0};

// --- FUNCIONES AUXILIARES ---

// Genera una palabra aleatoria de longitud L
static std::string random_word(int L, std::mt19937& rng) {
    std::string w(L, '0');
    std::uniform_int_distribution<int> dist(0, 1);
    for (int i = 0; i < L; ++i) {
        if (dist(rng)) w[i] = '1';
    }
    return w;
}

// Aplica CA (Símbolo)
static char apply_rule_bit(const std::string& word, int i, int r, int L, const std::vector<char>& rule_bits) {
    int idx = 0;
    for (int j = i - r; j <= i + r; ++j) {
        char b = '0';
        if (j >= 0 && j < L) b = word[j];
        idx = (idx << 1) | (b == '1' ? 1 : 0);
    }
    return rule_bits[idx];
}

// Aplica H completo (Símbolo + Estado)
static bool apply_H_single(const std::string& w, int pos, const std::string& q,
                           int r, int L, const std::vector<char>& rule_bits,
                           const std::array<int, 8>& perm,
                           std::string& w_out, int& pos_out, std::string& q_out) {
    w_out.resize(L);
    for(int i=0; i<L; ++i) {
        w_out[i] = apply_rule_bit(w, i, r, L, rule_bits);
    }
    int qi = state_index_from_label(q);
    if (qi < 0) return false;
    pos_out = pos;
    q_out = STATE_LABELS[perm[qi]];
    return true;
}

// Evalúa % de éxito de H o H (Involución)
// Retorna un double entre 0.0 y 1.0
static double score_involution(int r, int L, const std::vector<char>& rule_bits,
                               const std::array<int, 8>& perm,
                               std::mt19937& rng, int samples) {
    int successes = 0;
    std::uniform_int_distribution<int> dist_pos(0, L - 1);
    std::uniform_int_distribution<int> dist_state(0, 7);

    for (int i = 0; i < samples; ++i) {
        std::string w = random_word(L, rng);
        int pos = dist_pos(rng);
        std::string q = STATE_LABELS[dist_state(rng)];

        std::string w1, q1; int pos1;
        if (!apply_H_single(w, pos, q, r, L, rule_bits, perm, w1, pos1, q1)) continue;

        std::string w2, q2; int pos2;
        if (!apply_H_single(w1, pos1, q1, r, L, rule_bits, perm, w2, pos2, q2)) continue;

        if (w == w2 && pos == pos2 && q == q2) {
            successes++;
        }
    }
    return (double)successes / (double)samples;
}

// Evalúa % de éxito de la Fórmula T^-1 = H T H
static double score_formula(int r, int L, const std::vector<char>& rule_bits,
                            const std::array<int, 8>& perm,
                            std::mt19937& rng, int samples) {
    int successes = 0;
    std::uniform_int_distribution<int> dist_pos(0, L - 1);
    std::uniform_int_distribution<int> dist_state(0, 7);

    for (int i = 0; i < samples; ++i) {
        std::string w = random_word(L, rng);
        int pos = dist_pos(rng);
        std::string q = STATE_LABELS[dist_state(rng)];

        // Lado Izquierdo: T^-1(x)
        RunResult resInv = run_inversa(1, w, pos, q);
        if (!resInv.ok) continue; // Si T^-1 falla, ignoramos muestra o contamos como fallo según criterio (aquí ignoramos)

        // Lado Derecho: H(T(H(x)))
        // 1. H(x)
        std::string wH, qH; int posH;
        if (!apply_H_single(w, pos, q, r, L, rule_bits, perm, wH, posH, qH)) continue;

        // 2. T(H(x))
        RunResult resT = run_original(1, wH, posH, qH);
        if (!resT.ok) continue;

        // 3. H(T(H(x)))
        std::string wHTH, qHTH; int posHTH;
        if (!apply_H_single(resT.word_out, resT.pos_out, resT.state_out, r, L, rule_bits, perm, wHTH, posHTH, qHTH)) continue;

        // Comparar
        if (wHTH == resInv.word_out && posHTH == (int)resInv.pos_out && qHTH == resInv.state_out) {
            successes++;
        }
    }
    return (double)successes / (double)samples;
}

// Función auxiliar para imprimir la regla
static void log_solution(const std::string& filename, const std::vector<char>& rule_bits,
                         const std::array<int,8>& perm, int r, double inv_score, double form_score) {
    std::ofstream f(filename);
    f << "R=" << r << "\n";
    f << "Involution Score: " << inv_score * 100.0 << "%\n";
    f << "Formula Score: " << form_score * 100.0 << "%\n";
    f << "Permutation: ";
    for(int i : perm) f << STATE_LABELS[i] << " ";
    f << "\nRule Bits: ";
    for(char c : rule_bits) f << c;
    f << "\n";
}

// --- HILO MONITOR ---
void monitor_thread_func() {
    auto start_time = std::chrono::steady_clock::now();
    while (true) {
        std::this_thread::sleep_for(std::chrono::seconds(PRINT_INTERVAL_SEC));

        auto now = std::chrono::steady_clock::now();
        auto elapsed = std::chrono::duration_cast<std::chrono::minutes>(now - start_time).count();

        double current_best_inv = global_stats.best_involution_pct.load();
        double current_best_frm = global_stats.best_formula_pct.load();
        unsigned long long rst = global_stats.restarts.load();
        unsigned long long mut = global_stats.mutations_tried.load();

        std::cout << "\n[" << elapsed << " min] REPORTE DE PROGRESO (R=" << R_TARGET << ")\n";
        std::cout << "  > Mejor H o H encontrado: " << std::fixed << std::setprecision(4) << (current_best_inv * 100.0) << "%\n";
        std::cout << "  > Mejor Formula encontrada: " << std::fixed << std::setprecision(4) << (current_best_frm * 100.0) << "%\n";
        std::cout << "  > Reinicios totales: " << rst << "\n";
        std::cout << "  > Mutaciones probadas: " << mut << "\n";
        std::cout << "----------------------------------------" << std::endl;
    }
}

// --- HILO TRABAJADOR (HILL CLIMBING) ---
void worker_thread(int thread_id, std::vector<std::array<int,8>> perms, std::string logdir) {
    std::random_device rd;
    std::mt19937 rng(rd() + thread_id); // Semilla única por hilo

    int K = 2 * R_TARGET + 1;
    int S = 1 << K; // 128 bits para r=3
    int L = 2 * (2 * R_TARGET) + 1; // Longitud de cinta para pruebas

    // Distribuciones
    std::uniform_int_distribution<int> dist_bit_idx(0, S - 1);
    std::uniform_int_distribution<int> dist_perm_idx(0, perms.size() - 1);

    while (true) {
        // --- PASO 1: REINICIO ALEATORIO ---
        global_stats.restarts.fetch_add(1);

        // 1. Elegir permutación aleatoria (fija para este intento de escalada)
        std::array<int, 8> current_perm = perms[dist_perm_idx(rng)];

        // 2. Generar bits de regla aleatorios (balanceados o puros random)
        std::vector<char> current_rule(S);
        for(int i=0; i<S; ++i) current_rule[i] = (rng() % 2) ? '1' : '0';

        double current_inv_score = score_involution(R_TARGET, L, current_rule, current_perm, rng, SAMPLE_SIZE);

        // Actualizar global si es récord
        double global_best = global_stats.best_involution_pct.load();
        if (current_inv_score > global_best) {
            global_stats.best_involution_pct.store(current_inv_score);
        }

        int stagnation_counter = 0;

        // --- PASO 2: ESCALADA (HILL CLIMBING) ---
        while (stagnation_counter < MAX_STAGNATION) {
            global_stats.mutations_tried.fetch_add(1);

            // Mutar: invertir un bit al azar
            int flip_idx = dist_bit_idx(rng);
            current_rule[flip_idx] = (current_rule[flip_idx] == '1' ? '0' : '1');

            double new_inv_score = score_involution(R_TARGET, L, current_rule, current_perm, rng, SAMPLE_SIZE);

            // Criterio de aceptación:
            // Si mejora o iguala (para navegar mesetas), nos quedamos.
            // Si empeora, revertimos.
            if (new_inv_score >= current_inv_score) {
                current_inv_score = new_inv_score;
                // Si mejoró estrictamente, reseteamos estancamiento
                if (new_inv_score > current_inv_score) stagnation_counter = 0;
                else stagnation_counter++; // Si es igual, cuenta como estancamiento leve

                // Actualizar record global
                double gb = global_stats.best_involution_pct.load();
                if (current_inv_score > gb) global_stats.best_involution_pct.store(current_inv_score);
            } else {
                // Revertir cambio
                current_rule[flip_idx] = (current_rule[flip_idx] == '1' ? '0' : '1');
                stagnation_counter++;
            }

            // --- SI INVOLUCIÓN ES PERFECTA (o muy alta), PROBAR FORMULA ---
            if (current_inv_score >= 0.99) { // Umbral para pasar a fase 2
                double frm_score = score_formula(R_TARGET, L, current_rule, current_perm, rng, SAMPLE_SIZE);

                double gb_frm = global_stats.best_formula_pct.load();
                if (frm_score > gb_frm) {
                    global_stats.best_formula_pct.store(frm_score);

                    // Guardar hallazgo interesante
                    if (frm_score > 0.5) {
                        std::string fname = logdir + "/candidate_F" + std::to_string((int)(frm_score*100)) +
                                            "_I" + std::to_string((int)(current_inv_score*100)) +
                                            "_T" + std::to_string(thread_id) + "_" + std::to_string(rng()) + ".log";
                        log_solution(fname, current_rule, current_perm, R_TARGET, current_inv_score, frm_score);
                        std::cout << "\n!!! HALLAZGO EN HILO " << thread_id << ": Formula " << (frm_score*100) << "%\n";
                    }
                }

                // Si logramos la perfección, seguimos optimizando la formula en vez de la involución
                // (Pequeña variación de lógica: si Inv es 100%, solo aceptamos cambios que mantengan Inv 100% Y mejoren Formula)
                if (frm_score >= 0.999 && current_inv_score >= 0.999) {
                     std::string fname = logdir + "/SOLUTION_FOUND.log";
                     log_solution(fname, current_rule, current_perm, R_TARGET, current_inv_score, frm_score);
                     std::cout << "\n!!! SOLUCIÓN ENCONTRADA !!!\n";
                     exit(0);
                }
            }
        }
        // Fin del while de escalada -> Reinicio aleatorio (Random Restart)
    }
}

// Generación de permutaciones (copiado y adaptado de tu código anterior)
static void involutive_permutations_dfs(int n, std::vector<bool>& used, std::array<int,8>& p, int i, std::vector<std::array<int,8>>& out) {
    while (i < n && used[i]) ++i;
    if (i == n) { out.push_back(p); return; }
    used[i] = true; p[i] = i;
    involutive_permutations_dfs(n, used, p, i + 1, out);
    p[i] = -1;
    for (int j = i + 1; j < n; ++j) {
        if (!used[j]) {
            used[j] = true; p[i] = j; p[j] = i;
            involutive_permutations_dfs(n, used, p, i + 1, out);
            p[j] = -1; used[j] = false;
        }
    }
    used[i] = false;
}

int main() {
    std::string logdir = "logs_opt_r3";
    std::filesystem::create_directories(logdir);

    std::cout << "Generando permutaciones involutivas..." << std::endl;
    std::vector<std::array<int,8>> perms;
    {
        std::vector<bool> used(8, false);
        std::array<int,8> p; p.fill(-1);
        involutive_permutations_dfs(8, used, p, 0, perms);
    }
    std::cout << "Permutaciones: " << perms.size() << "\n";
    std::cout << "Iniciando optimizacion heuristica para r=" << R_TARGET << "\n";
    std::cout << "Nucleos disponibles: " << std::thread::hardware_concurrency() << "\n";
    std::cout << "Reporte cada 5 minutos..." << std::endl;

    // Hilo de monitoreo
    std::thread monitor(monitor_thread_func);
    monitor.detach();

    // Hilos trabajadores
    unsigned int n_workers = std::thread::hardware_concurrency();
    if (n_workers == 0) n_workers = 4;

    std::vector<std::thread> workers;
    for(unsigned int i=0; i<n_workers; ++i) {
        workers.emplace_back(worker_thread, i, perms, logdir);
    }

    for(auto& t : workers) t.join();

    return 0;
}