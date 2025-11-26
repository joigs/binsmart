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

// ===================== Utilidades ======================

struct RunConfig {
    std::string logdir = "logs_tmt";
    long long   progress_interval = 100000;   // cada cuántos H reportar progreso
    int         threads = 0;                  // 0 => usar hardware_concurrency()
};

static bool apply_symbol_CA(const std::string& word,
                            int r,
                            int neighborhood_len,
                            const std::vector<char>& rule_bits,
                            std::string& out)
{
    int L = static_cast<int>(word.size());
    out.clear();
    out.reserve(L);

    int K = neighborhood_len;
    int S = static_cast<int>(rule_bits.size());
    if (S != (1 << K)) return false;

    for (int i = 0; i < L; ++i) {
        int idx = 0;
        for (int j = i - r; j <= i + r; ++j) {
            char b = '0';
            if (j >= 0 && j < L) b = word[j];
            idx = (idx << 1) | (b == '1' ? 1 : 0);
        }
        char v = rule_bits[idx];
        out.push_back(v);
    }
    return true;
}

static bool apply_H_TMT(const std::string& word,
                        int pos,
                        const std::string& qlbl,
                        int r,
                        int neighborhood_len,
                        const std::vector<char>& rule_bits,
                        const std::array<int,8>& perm,
                        std::string& w2,
                        int& pos2,
                        std::string& q2)
{
    if (!apply_symbol_CA(word, r, neighborhood_len, rule_bits, w2)) return false;
    int qi = state_index_from_label(qlbl);
    if (qi < 0) return false;
    int qnext = perm[qi];
    pos2 = pos;
    q2   = STATE_LABELS[qnext];
    return true;
}

static std::string fmt_rule_bits_table(const std::vector<char>& rule_bits,
                                       int r,
                                       int neighborhood_len)
{
    std::ostringstream oss;
    oss << "SIMBOLOS r=" << r << "\n";
    int S = static_cast<int>(rule_bits.size());
    int K = neighborhood_len;
    for (int idx = 0; idx < S; ++idx) {
        std::string key(K, '0');
        for (int b = 0; b < K; ++b) {
            int bitpos = K - 1 - b;
            char c = (idx & (1 << bitpos)) ? '1' : '0';
            key[b] = c;
        }
        std::string left, center, right;
        if (K == 3) {
            left   = key.substr(0, 1);
            center = key.substr(1, 1);
            right  = key.substr(2);
        } else {
            int mid = K / 2;
            left   = key.substr(0, mid);
            center = key.substr(mid, 1);
            right  = key.substr(mid + 1);
        }
        oss << "  (" << left << "|" << center << "|" << right
            << ") -> " << rule_bits[idx] << "\n";
    }
    return oss.str();
}

static std::string fmt_perm(const std::array<int,8>& perm) {
    std::ostringstream oss;
    oss << "ESTADOS sigma (involucion)\n";
    for (int i = 0; i < 8; ++i) {
        oss << "  " << STATE_LABELS[i] << " -> " << STATE_LABELS[perm[i]] << "\n";
    }
    return oss.str();
}

// ==================== Verificación H∘H ====================

static bool verify_involution_over_tapes(int r,
                                         int L,
                                         int neighborhood_len,
                                         const std::vector<char>& rule_bits,
                                         const std::array<int,8>& perm,
                                         std::ostream* logp)
{
    if (L <= 0 || L >= 63) return false;

    unsigned long long words = 1ULL << L;
    unsigned long long ti    = 0;  // índice global de configuración

    for (unsigned long long mask = 0; mask < words; ++mask) {
        std::string w(L, '0');
        for (int i = 0; i < L; ++i) {
            unsigned long long bit = 1ULL << (L - 1 - i);
            if (mask & bit) w[i] = '1';
        }
        for (int pos = 0; pos < L; ++pos) {
            for (int qi = 0; qi < 8; ++qi) {
                const std::string& q = STATE_LABELS[qi];

                std::string w1;
                int         pos1;
                std::string q1;
                if (!apply_H_TMT(w, pos, q, r, neighborhood_len,
                                 rule_bits, perm, w1, pos1, q1)) {
                    if (logp) {
                        (*logp) << "x#" << ti << " H indefinida | x=("
                                << w << "; head=" << pos << "; state=" << q << ")\n";
                    }
                    return false;
                }

                std::string w2;
                int         pos2;
                std::string q2;
                if (!apply_H_TMT(w1, pos1, q1, r, neighborhood_len,
                                 rule_bits, perm, w2, pos2, q2)) {
                    if (logp) {
                        (*logp) << "x#" << ti << " H∘H indefinida | x=("
                                << w << "; head=" << pos << "; state=" << q
                                << ") | Hx=(" << w1 << "; " << pos1 << "; " << q1
                                << ")\n";
                    }
                    return false;
                }

                if (!(w2 == w && pos2 == pos && q2 == q)) {
                    if (logp) {
                        (*logp) << "x#" << ti << " H∘H(x) != x\n";
                        (*logp) << "x    = (" << w << "; head=" << pos
                                << "; state=" << q << ")\n";
                        (*logp) << "Hx   = (" << w1 << "; head=" << pos1
                                << "; state=" << q1 << ")\n";
                        (*logp) << "HHx  = (" << w2 << "; head=" << pos2
                                << "; state=" << q2 << ")\n";
                    }
                    return false;
                }

                ++ti;
            }
        }
    }
    return true;
}

// =============== Verificación T^{-1} = H∘T∘H =================

static bool verify_conjugacy_over_tapes(int r,
                                        int L,
                                        int neighborhood_len,
                                        const std::vector<char>& rule_bits,
                                        const std::array<int,8>& perm,
                                        std::ostream* logp)
{
    if (L <= 0 || L >= 63) return false;

    unsigned long long words = 1ULL << L;
    unsigned long long ti    = 0;

    for (unsigned long long mask = 0; mask < words; ++mask) {
        std::string w(L, '0');
        for (int i = 0; i < L; ++i) {
            unsigned long long bit = 1ULL << (L - 1 - i);
            if (mask & bit) w[i] = '1';
        }
        for (int pos = 0; pos < L; ++pos) {
            for (int qi = 0; qi < 8; ++qi) {
                const std::string& q = STATE_LABELS[qi];

                // H(x)
                std::string wH; int posH; std::string qH;
                if (!apply_H_TMT(w, pos, q, r, neighborhood_len,
                                 rule_bits, perm, wH, posH, qH)) {
                    if (logp) {
                        (*logp) << "x#" << ti << " H indefinida\n";
                    }
                    return false;
                }

                // T(H(x))
                RunResult resT = run_original(1, wH, posH, qH);
                if (!resT.ok) {
                    if (logp) {
                        (*logp) << "x#" << ti << " T fallo\n";
                    }
                    return false;
                }
                std::string wTH  = resT.word_out;
                int         posTH = (int)resT.pos_out;
                std::string qTH  = resT.state_out;

                // H(T(H(x)))
                std::string wHTH; int posHTH; std::string qHTH;
                if (!apply_H_TMT(wTH, posTH, qTH, r, neighborhood_len,
                                 rule_bits, perm, wHTH, posHTH, qHTH)) {
                    if (logp) {
                        (*logp) << "x#" << ti << " H en T(H(x)) indefinida\n";
                    }
                    return false;
                }

                // T^{-1}(x)
                RunResult resInv = run_inversa(1, w, pos, q);
                if (!resInv.ok) {
                    if (logp) {
                        (*logp) << "x#" << ti << " T^-1 fallo\n";
                    }
                    return false;
                }
                std::string wInv   = resInv.word_out;
                int         posInv = (int)resInv.pos_out;
                std::string qInv   = resInv.state_out;

                if (!(wHTH == wInv && posHTH == posInv && qHTH == qInv)) {
                    if (logp) {
                        (*logp) << "x#" << ti
                                << " no cumple T^-1 = H∘T∘H\n";
                        (*logp) << "x     = (" << w << ";" << pos << ";" << q << ")\n";
                        (*logp) << "Hx    = (" << wH << ";" << posH << ";" << qH << ")\n";
                        (*logp) << "THx   = (" << wTH << ";" << posTH << ";" << qTH << ")\n";
                        (*logp) << "HTHx  = (" << wHTH << ";" << posHTH << ";" << qHTH << ")\n";
                        (*logp) << "Tinvx = (" << wInv << ";" << posInv << ";" << qInv << ")\n";
                    }
                    return false;
                }

                ++ti;
            }
        }
    }

    return true;
}

// =================== Involuciones de estados ===================

static void involutive_permutations_dfs(int n,
                                        std::vector<bool>& used,
                                        std::array<int,8>& p,
                                        int i,
                                        std::vector<std::array<int,8>>& out)
{
    while (i < n && used[i]) ++i;
    if (i == n) {
        out.push_back(p);
        return;
    }
    used[i] = true;
    p[i] = i;
    involutive_permutations_dfs(n, used, p, i + 1, out);
    p[i] = -1;
    for (int j = i + 1; j < n; ++j) {
        if (!used[j]) {
            used[j] = true;
            p[i] = j;
            p[j] = i;
            involutive_permutations_dfs(n, used, p, i + 1, out);
            p[j] = -1;
            used[j] = false;
        }
    }
    used[i] = false;
}

static std::vector<std::array<int,8>> generate_involutive_permutations_8() {
    int n = 8;
    std::vector<std::array<int,8>> out;
    std::vector<bool> used(n, false);
    std::array<int,8> p;
    for (int i = 0; i < n; ++i) p[i] = -1;
    involutive_permutations_dfs(n, used, p, 0, out);
    return out;
}

static long long count_involutive_perms_8() {
    int n = 8;
    std::vector<long long> fact(n + 1);
    fact[0] = 1;
    for (int i = 1; i <= n; ++i) fact[i] = fact[i - 1] * i;
    long long total = 0;
    for (int k = 0; k <= n / 2; ++k) {
        long long num = fact[n];
        long long den = fact[k] * ((1LL << k)) * fact[n - 2 * k];
        total += num / den;
    }
    return total;
}

// ======================= Combinaciones ========================

template<typename F>
static void for_each_combination(int n, int k, F f) {
    if (k < 0 || k > n) return;
    if (k == 0) {
        std::vector<int> empty;
        f(empty);
        return;
    }
    std::vector<int> comb(k);
    for (int i = 0; i < k; ++i) comb[i] = i;
    while (true) {
        f(comb);
        int i;
        for (i = k - 1; i >= 0; --i) {
            if (comb[i] != i + n - k) break;
        }
        if (i < 0) break;
        ++comb[i];
        for (int j = i + 1; j < k; ++j) comb[j] = comb[j - 1] + 1;
    }
}

// ====================== main ===========================

int main(int argc, char** argv) {
    RunConfig cfg;

    // Parámetros: --logdir, --progress-interval, --threads
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--logdir" && i + 1 < argc) {
            cfg.logdir = argv[++i];
        } else if (arg == "--progress-interval" && i + 1 < argc) {
            cfg.progress_interval = std::stoll(argv[++i]);
        } else if (arg == "--threads" && i + 1 < argc) {
            cfg.threads = std::stoi(argv[++i]);
        }
    }

    std::filesystem::create_directories(cfg.logdir);

    long long inv_count = count_involutive_perms_8();
    std::vector<std::array<int,8>> perms = generate_involutive_permutations_8();

    std::atomic<bool> found(false);
    std::mutex        shared_mutex;     // para imprimir y copiar datos de la H encontrada

    // Datos de la H encontrada (para re-loguear al final)
    int                    found_r    = -1;
    int                    found_L    = -1;
    int                    found_K    = -1;
    long long              found_hidx = -1;
    std::vector<char>      found_rule_bits;
    std::array<int,8>      found_perm{};

    int r = 1;
    while (!found.load()) {
        int d = 2 * r;
        int L = 2 * d + 1;
        int K = 2 * r + 1;
        int S = 1 << K;

        std::filesystem::path rdir =
            std::filesystem::path(cfg.logdir) / ("r" + std::to_string(r));
        std::filesystem::create_directories(rdir);

        long double num_sym_bal = 0.0L;
        if (S % 2 == 0) {
            int half = S / 2;
            long double c = 1.0L;
            for (int i = 1; i <= half; ++i) {
                c *= static_cast<long double>(S + 1 - i);
                c /= static_cast<long double>(i);
            }
            num_sym_bal = c;
        }
        long double total_H = num_sym_bal * static_cast<long double>(inv_count);

        {
            std::lock_guard<std::mutex> lock(shared_mutex);
            std::cout << "Iniciando r=" << r
                      << ", L=" << L
                      << ", H_balanceadas_max=" << static_cast<long double>(total_H)
                      << "\n";
            std::cout.flush();
        }

        std::atomic<long long> tested(0);
        long long sym_rule_idx = 0;
        int half = S / 2;

        // Para cada regla de símbolos balanceada
        for_each_combination(S, half, [&](const std::vector<int>& ones) {
            if (found.load()) return;

            std::vector<char> rule_bits(S, '0');
            for (int idx : ones) rule_bits[idx] = '1';

            long long base_idx = sym_rule_idx * inv_count;
            sym_rule_idx++;

            // Configuración de hilos
            unsigned int thread_count = (cfg.threads > 0)
                                        ? (unsigned int)cfg.threads
                                        : std::thread::hardware_concurrency();
            if (thread_count == 0) thread_count = 1;

            std::atomic<std::size_t> next_perm(0);
            std::vector<std::thread> threads;
            threads.reserve(thread_count);

            for (unsigned int t = 0; t < thread_count; ++t) {
                threads.emplace_back([&, base_idx]() {
                    int neighborhood_len = K;

                    while (true) {
                        if (found.load()) return;

                        std::size_t p_idx = next_perm.fetch_add(1);
                        if (p_idx >= perms.size()) return;

                        long long h_idx = base_idx + (long long)p_idx + 1;
                        long long tnum  = tested.fetch_add(1) + 1;

                        if (cfg.progress_interval > 0 &&
                            tnum % cfg.progress_interval == 0) {
                            std::lock_guard<std::mutex> lock(shared_mutex);
                            std::cout << "r=" << r
                                      << " progreso: " << tnum
                                      << " de " << static_cast<long double>(total_H)
                                      << "\n";
                            std::cout.flush();
                        }

                        // Primero comprobamos H∘H sin logs
                        bool invol_ok = verify_involution_over_tapes(
                            r, L, neighborhood_len, rule_bits, perms[p_idx],
                            nullptr
                        );
                        if (!invol_ok) {
                            continue;
                        }

                        // Luego la fórmula T^{-1} = H∘T∘H sin logs
                        bool conj_ok = verify_conjugacy_over_tapes(
                            r, L, neighborhood_len, rule_bits, perms[p_idx],
                            nullptr
                        );
                        if (!conj_ok) {
                            continue;
                        }

                        // Pasó todo. Intentamos marcar como encontrada.
                        bool expected = false;
                        if (found.compare_exchange_strong(expected, true)) {
                            // Guardamos los datos de esta H
                            {
                                std::lock_guard<std::mutex> lock(shared_mutex);
                                found_r    = r;
                                found_L    = L;
                                found_K    = neighborhood_len;
                                found_hidx = h_idx;
                                found_rule_bits = rule_bits;
                                found_perm      = perms[p_idx];

                                std::cout << "H encontrada (sin log aun) en r="
                                          << r << ", H_idx=" << h_idx << "\n";
                                std::cout.flush();
                            }
                        }

                        return; // este hilo ya no necesita seguir
                    }
                });
            }

            for (auto& th : threads) th.join();

            if (found.load()) return;
        });

        if (!found.load()) {
            std::lock_guard<std::mutex> lock(shared_mutex);
            std::cout << "Terminado r=" << r << " sin encontrar H\n";
            std::cout.flush();
        }

        ++r;
    }

    // Si llegamos aquí, found == true y tenemos almacenada la H ganadora.
    if (found_r >= 0) {
        int rfin = found_r;
        int Lfin = found_L;
        int Kfin = found_K;

        std::filesystem::path rdir =
            std::filesystem::path(cfg.logdir) / ("r" + std::to_string(rfin));
        std::filesystem::create_directories(rdir);

        std::filesystem::path fpath =
            rdir / ("H_" + std::to_string(found_hidx) + ".log");
        std::ofstream f(fpath);
        if (f) {
            f << fmt_rule_bits_table(found_rule_bits, rfin, Kfin) << "\n";
            f << fmt_perm(found_perm) << "\n";

            // Re-ejecutamos verificaciones pero ahora escribiendo log completo
            bool inv_ok = verify_involution_over_tapes(
                rfin, Lfin, Kfin, found_rule_bits, found_perm, &f
            );
            bool conj_ok = false;
            if (inv_ok) {
                conj_ok = verify_conjugacy_over_tapes(
                    rfin, Lfin, Kfin, found_rule_bits, found_perm, &f
                );
            }

            if (inv_ok && conj_ok) {
                f << "ENCONTRADA\n";
            } else {
                f << "ADVERTENCIA: fallo al re-verificar H encontrada\n";
            }
            f.flush();

            std::lock_guard<std::mutex> lock(shared_mutex);
            std::cout << "H encontrada en r=" << rfin
                      << ", archivo=" << fpath.string() << "\n";
            std::cout.flush();
        } else {
            std::lock_guard<std::mutex> lock(shared_mutex);
            std::cout << "H encontrada en r=" << rfin
                      << ", pero no se pudo abrir el log "
                      << fpath.string() << "\n";
            std::cout.flush();
        }
    }

    return 0;
}
