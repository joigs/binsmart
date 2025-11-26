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
#include <streambuf>

struct NullBuffer : public std::streambuf {
    int overflow(int c) override { return c; }
};

struct ConjugacyResult {
    bool full_ok;                  // true si pasó todas las configuraciones
    unsigned long long succeeded;  // cuántas configuraciones cumplieron la fórmula
    unsigned long long total;      // total de configuraciones
};

static bool apply_symbol_CA(const std::string& word, int r, int neighborhood_len,
                            const std::vector<char>& rule_bits, std::string& out) {
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

static bool apply_H_TMT(const std::string& word, int pos, const std::string& qlbl,
                        int r, int neighborhood_len, const std::vector<char>& rule_bits,
                        const std::array<int,8>& perm,
                        std::string& w2, int& pos2, std::string& q2) {
    if (!apply_symbol_CA(word, r, neighborhood_len, rule_bits, w2)) return false;
    int qi = state_index_from_label(qlbl);
    if (qi < 0) return false;
    int qnext = perm[qi];
    pos2 = pos;
    q2 = STATE_LABELS[qnext];
    return true;
}

static std::string fmt_rule_bits_table(const std::vector<char>& rule_bits,
                                       int r, int neighborhood_len) {
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

// H∘H: muestreo uniforme de ejemplos “ok H∘H” para no inflar el log
static bool verify_involution_over_tapes(int r, int L, int neighborhood_len,
                                         const std::vector<char>& rule_bits,
                                         const std::array<int,8>& perm,
                                         std::ostream& logf) {
    if (L <= 0 || L >= 63) return false;
    unsigned long long words = 1ULL << L;
    unsigned long long total_x = words * (unsigned long long)L * 8ULL;

    const std::size_t MAX_OK_LOG_INV = 100;  // nº máximo de ejemplos “ok H∘H” por H
    unsigned long long stride = (MAX_OK_LOG_INV > 0 && total_x > MAX_OK_LOG_INV)
                              ? (total_x / MAX_OK_LOG_INV)
                              : 1ULL;
    std::size_t ok_logged = 0;

    unsigned long long ti = 0;  // índice global de configuración
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
                int pos1;
                std::string q1;
                if (!apply_H_TMT(w, pos, q, r, neighborhood_len,
                                  rule_bits, perm, w1, pos1, q1)) {
                    logf << "x#" << ti << " H indefinida | x=("
                         << w << "; head=" << pos << "; state=" << q << ")\n";
                    return false;
                }
                std::string w2;
                int pos2;
                std::string q2;
                if (!apply_H_TMT(w1, pos1, q1, r, neighborhood_len,
                                  rule_bits, perm, w2, pos2, q2)) {
                    logf << "x#" << ti << " H∘H indefinida | x=("
                         << w << "; head=" << pos << "; state=" << q
                         << ") | Hx=(" << w1 << "; " << pos1 << "; " << q1 << ")\n";
                    return false;
                }
                if (!(w2 == w && pos2 == pos && q2 == q)) {
                    logf << "x#" << ti << " H∘H(x) != x\n";
                    logf << "x    = (" << w << "; head=" << pos << "; state=" << q << ")\n";
                    logf << "Hx   = (" << w1 << "; head=" << pos1 << "; state=" << q1 << ")\n";
                    logf << "HHx  = (" << w2 << "; head=" << pos2 << "; state=" << q2 << ")\n";
                    return false;
                }

                if (ok_logged < MAX_OK_LOG_INV && (ti % stride == 0)) {
                    logf << "x#" << ti << " ok H∘H | x=("
                         << w << ";" << pos << ";" << q
                         << ") | Hx=(" << w1 << ";" << pos1 << ";" << q1
                         << ") | HHx=(" << w2 << ";" << pos2 << ";" << q2 << ")\n";
                    ++ok_logged;
                }

                ++ti;
            }
        }
    }
    return true;
}

// Fórmula T^{-1} = H∘T∘H, con muestreo + contadores para clasificación
static ConjugacyResult verify_conjugacy_over_tapes(
    int r, int L, int neighborhood_len,
    const std::vector<char>& rule_bits,
    const std::array<int,8>& perm,
    std::ostream& logf
) {
    ConjugacyResult res;
    res.full_ok   = false;
    res.succeeded = 0;
    res.total     = 0;

    if (L <= 0 || L >= 63) return res;

    unsigned long long words = 1ULL << L;
    unsigned long long total_x = words * (unsigned long long)L * 8ULL;
    res.total = total_x;

    const std::size_t MAX_OK_LOG = 64;  // nº máximo de ejemplos “ok formula” por H
    unsigned long long stride = (MAX_OK_LOG > 0 && total_x > MAX_OK_LOG)
                              ? (total_x / MAX_OK_LOG)
                              : 1ULL;
    std::size_t ok_logged = 0;

    unsigned long long ti = 0;
    for (unsigned long long mask = 0; mask < words; ++mask) {
        std::string w(L, '0');
        for (int i = 0; i < L; ++i) {
            unsigned long long bit = 1ULL << (L - 1 - i);
            if (mask & bit) w[i] = '1';
        }
        for (int pos = 0; pos < L; ++pos) {
            for (int qi = 0; qi < 8; ++qi) {
                const std::string& q = STATE_LABELS[qi];

                std::string wH; int posH; std::string qH;
                if (!apply_H_TMT(w, pos, q, r, neighborhood_len,
                                  rule_bits, perm, wH, posH, qH)) {
                    logf << "x#" << ti << " H indefinida\n";
                    return res;  // succeeded se mantiene
                }

                RunResult resT = run_original(1, wH, posH, qH);
                if (!resT.ok) {
                    logf << "x#" << ti << " T fallo\n";
                    return res;
                }
                std::string wTH  = resT.word_out;
                int         posTH = (int)resT.pos_out;
                std::string qTH  = resT.state_out;

                std::string wHTH; int posHTH; std::string qHTH;
                if (!apply_H_TMT(wTH, posTH, qTH, r, neighborhood_len,
                                  rule_bits, perm, wHTH, posHTH, qHTH)) {
                    logf << "x#" << ti << " H en T(H(x)) indefinida\n";
                    return res;
                }

                RunResult resInv = run_inversa(1, w, pos, q);
                if (!resInv.ok) {
                    logf << "x#" << ti << " T^-1 fallo\n";
                    return res;
                }
                std::string wInv  = resInv.word_out;
                int         posInv = (int)resInv.pos_out;
                std::string qInv  = resInv.state_out;

                if (!(wHTH == wInv && posHTH == posInv && qHTH == qInv)) {
                    logf << "x#" << ti << " no cumple T^-1 = H∘T∘H\n";
                    logf << "x     = (" << w << ";" << pos << ";" << q << ")\n";
                    logf << "Hx    = (" << wH << ";" << posH << ";" << qH << ")\n";
                    logf << "THx   = (" << wTH << ";" << posTH << ";" << qTH << ")\n";
                    logf << "HTHx  = (" << wHTH << ";" << posHTH << ";" << qHTH << ")\n";
                    logf << "Tinvx = (" << wInv << ";" << posInv << ";" << qInv << ")\n";
                    return res;
                }

                ++res.succeeded;

                if (ok_logged < MAX_OK_LOG && (ti % stride == 0)) {
                    logf << "x#" << ti << " ok formula | x=("
                         << w << ";" << pos << ";" << q << ")\n";
                    ++ok_logged;
                }

                ++ti;
            }
        }
    }

    res.full_ok = true;
    return res;
}

static void involutive_permutations_dfs(int n,
                                        std::vector<bool>& used,
                                        std::array<int,8>& p,
                                        int i,
                                        std::vector<std::array<int,8>>& out) {
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

int main(int argc, char** argv) {
    std::string logdir = "logs_tmt";
    long long progress_interval = 100000;
    unsigned int requested_threads = 0; // 0 => usar hardware_concurrency

    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--logdir" && i + 1 < argc) {
            logdir = argv[++i];
        } else if (arg == "--progress-interval" && i + 1 < argc) {
            progress_interval = std::stoll(argv[++i]);
        } else if (arg == "--threads" && i + 1 < argc) {
            requested_threads = static_cast<unsigned int>(std::stoul(argv[++i]));
        }
    }

    std::filesystem::create_directories(logdir);
    long long inv_count = count_involutive_perms_8();
    std::vector<std::array<int,8>> perms = generate_involutive_permutations_8();

    std::atomic<bool> found(false);
    std::string found_path;
    int found_r = -1;
    std::mutex io_mutex;

    unsigned int hw = std::thread::hardware_concurrency();
    {
        std::lock_guard<std::mutex> lock(io_mutex);
        std::cout << "hardware_concurrency=" << hw << "\n";
        if (requested_threads > 0)
            std::cout << "threads solicitados=" << requested_threads << "\n";
        std::cout.flush();
    }

    int r = 1;
    while (true) {
        int d = 2 * r;
        int L = 2 * d + 1;
        std::filesystem::path rdir =
            std::filesystem::path(logdir) / ("r" + std::to_string(r));
        std::filesystem::create_directories(rdir);
        std::filesystem::path formula_rdir = rdir / "formula";
        std::filesystem::create_directories(formula_rdir);

        int K = 2 * r + 1;
        int S = 1 << K;

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
            std::lock_guard<std::mutex> lock(io_mutex);
            std::cout << "Iniciando r=" << r
                      << ", L=" << L
                      << ", H_balanceadas_max=" << static_cast<long double>(total_H)
                      << "\n";
            std::cout.flush();
        }

        std::atomic<long long> tested(0);
        long long sym_rule_idx = 0;
        int half = S / 2;

        for_each_combination(S, half, [&](const std::vector<int>& ones) {
            if (found.load()) return;

            std::vector<char> rule_bits(S, '0');
            for (int idx : ones) rule_bits[idx] = '1';

            long long base_idx = sym_rule_idx * inv_count;
            sym_rule_idx++;

            unsigned int thread_count = requested_threads;
            if (thread_count == 0) {
                thread_count = std::thread::hardware_concurrency();
                if (thread_count == 0) thread_count = 1;
            }
            if (thread_count > perms.size())
                thread_count = static_cast<unsigned int>(perms.size());

            std::vector<std::thread> threads;
            threads.reserve(thread_count);

            for (unsigned int t = 0; t < thread_count; ++t) {
                threads.emplace_back([&, t, base_idx, thread_count]() {
                    int neighborhood_len = K;
                    NullBuffer nbuf;
                    std::ostream devnull(&nbuf);

                    std::size_t nperms = perms.size();
                    std::size_t start = (nperms * t) / thread_count;
                    std::size_t end   = (nperms * (t + 1)) / thread_count;

                    for (std::size_t p_idx = start; p_idx < end; ++p_idx) {
                        if (found.load()) return;

                        long long h_idx = base_idx + static_cast<long long>(p_idx) + 1;
                        long long tnum = tested.fetch_add(1) + 1;

                        if (progress_interval > 0 && tnum % progress_interval == 0) {
                            std::lock_guard<std::mutex> lock(io_mutex);
                            std::cout << "r=" << r << " progreso: "
                                      << tnum << " de "
                                      << static_cast<long double>(total_H) << "\n";
                            std::cout.flush();
                        }

                        bool log_main = (progress_interval > 0 &&
                                         (tnum % progress_interval == 0));

                        std::filesystem::path main_fpath;
                        std::ofstream main_log;
                        std::ostream* main_logp = &devnull;

                        if (log_main) {
                            main_fpath = rdir / ("H_" + std::to_string(h_idx) + ".log");
                            main_log.open(main_fpath);
                            if (main_log) {
                                main_log << fmt_rule_bits_table(rule_bits, r, neighborhood_len)
                                         << "\n";
                                main_log << fmt_perm(perms[p_idx]) << "\n";
                                main_logp = &main_log;
                            } else {
                                log_main = false;
                                main_logp = &devnull;
                            }
                        }

                        bool invol_ok = verify_involution_over_tapes(
                            r, L, neighborhood_len, rule_bits, perms[p_idx],
                            *main_logp
                        );
                        if (!invol_ok) {
                            continue;
                        }

                        // Llegó al punto de intentar la fórmula:
                        // log temporal en formula_rdir, luego se reclasifica si pasa >=75%
                        std::filesystem::path tmp_fpath =
                            formula_rdir / ("H_" + std::to_string(h_idx) + ".log.tmp");
                        std::ofstream formula_log(tmp_fpath);
                        if (!formula_log) {
                            // No se pudo abrir log de fórmula, pero igual probamos sin log
                            NullBuffer nbuf2;
                            std::ostream devnull2(&nbuf2);
                            bool inv2 = verify_involution_over_tapes(
                                r, L, neighborhood_len, rule_bits, perms[p_idx],
                                devnull2
                            );
                            if (!inv2) continue;
                            ConjugacyResult cr2 = verify_conjugacy_over_tapes(
                                r, L, neighborhood_len, rule_bits, perms[p_idx],
                                devnull2
                            );
                            if (cr2.full_ok) {
                                bool expected = false;
                                if (found.compare_exchange_strong(expected, true)) {
                                    std::lock_guard<std::mutex> lock(io_mutex);
                                    found_path = tmp_fpath.string();
                                    found_r = r;
                                    std::cout << "H encontrada en r=" << r
                                              << ", pero no se pudo escribir log\n";
                                    std::cout.flush();
                                }
                            }
                            return;
                        }

                        // Encabezado en log de fórmula
                        formula_log << fmt_rule_bits_table(rule_bits, r, neighborhood_len)
                                    << "\n";
                        formula_log << fmt_perm(perms[p_idx]) << "\n";

                        bool invol_ok2 = verify_involution_over_tapes(
                            r, L, neighborhood_len, rule_bits, perms[p_idx],
                            formula_log
                        );
                        if (!invol_ok2) {
                            formula_log.flush();
                            formula_log.close();
                            std::error_code ec_rm;
                            std::filesystem::remove(tmp_fpath, ec_rm);
                            continue;
                        }

                        ConjugacyResult cr = verify_conjugacy_over_tapes(
                            r, L, neighborhood_len, rule_bits, perms[p_idx],
                            formula_log
                        );

                        formula_log.flush();
                        formula_log.close();

                        // Clasificación: solo guardamos si pasa >= 75% de las combinaciones
                        long double ratio = 0.0L;
                        if (cr.total > 0) {
                            ratio = (long double)cr.succeeded / (long double)cr.total;
                        }

                        if (!cr.full_ok && ratio < 0.75L) {
                            // Pasa menos del 75%: no nos interesa, borramos el log
                            std::error_code ec_rm;
                            std::filesystem::remove(tmp_fpath, ec_rm);
                            continue;
                        }

                        // Aquí ratio >= 0.75 o full_ok
                        std::filesystem::path target_dir = formula_rdir / "75";
                        if (cr.full_ok) {
                            target_dir /= "100";
                        }

                        std::error_code ec_mk;
                        std::filesystem::create_directories(target_dir, ec_mk);

                        std::filesystem::path formula_fpath =
                            target_dir / ("H_" + std::to_string(h_idx) + ".log");

                        std::error_code ec_mv;
                        std::filesystem::rename(tmp_fpath, formula_fpath, ec_mv);

                        if (!cr.full_ok) {
                            // No cumple la fórmula al 100%; solo nos interesa para análisis,
                            // pero no detenemos la búsqueda.
                            continue;
                        }

                        // H cumple la fórmula en todas las configuraciones
                        bool expected = false;
                        if (found.compare_exchange_strong(expected, true)) {
                            // Somos el primer hilo en encontrar un H válido
                            if (!log_main) {
                                // No se había generado log principal, lo creamos ahora
                                main_fpath = rdir / ("H_" + std::to_string(h_idx) + ".log");
                                std::ofstream mf(main_fpath);
                                if (mf) {
                                    mf << fmt_rule_bits_table(rule_bits, r, neighborhood_len)
                                       << "\n";
                                    mf << fmt_perm(perms[p_idx]) << "\n";
                                    verify_involution_over_tapes(
                                        r, L, neighborhood_len, rule_bits, perms[p_idx],
                                        mf
                                    );
                                    verify_conjugacy_over_tapes(
                                        r, L, neighborhood_len, rule_bits, perms[p_idx],
                                        mf
                                    );
                                    mf << "ENCONTRADA\n";
                                    mf.flush();
                                }
                            } else {
                                if (main_log) {
                                    main_log << "ENCONTRADA\n";
                                    main_log.flush();
                                }
                            }

                            {
                                std::lock_guard<std::mutex> lock(io_mutex);
                                found_path = formula_fpath.string();
                                found_r = r;
                                std::cout << "H encontrada en r=" << r
                                          << ", archivo=" << found_path << "\n";
                                std::cout.flush();
                            }
                        }

                        return;  // este hilo ya no necesita seguir procesando más perms
                    }
                });
            }

            for (auto& th : threads) th.join();
        });

        if (found.load()) break;

        {
            std::lock_guard<std::mutex> lock(io_mutex);
            std::cout << "Terminado r=" << r << " sin encontrar H\n";
            std::cout.flush();
        }

        r += 1;
    }

    return 0;
}
