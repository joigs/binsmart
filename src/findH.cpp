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
#include <streambuf>

struct NullBuffer : public std::streambuf {
    int overflow(int c) override { return c; }
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

static bool verify_involution_over_tapes(int r, int L, int neighborhood_len,
                                         const std::vector<char>& rule_bits,
                                         const std::array<int,8>& perm,
                                         std::ostream& logf) {
    if (L <= 0 || L >= 63) return false;
    unsigned long long words = 1ULL << L;
    std::size_t ti = 0;
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
                if (ti < 10) {
                    logf << "x#" << ti << " ok H∘H | x=("
                         << w << ";" << pos << ";" << q
                         << ") | Hx=(" << w1 << ";" << pos1 << ";" << q1
                         << ") | HHx=(" << w2 << ";" << pos2 << ";" << q2 << ")\n";
                }
                ++ti;
            }
        }
    }
    return true;
}

static bool verify_conjugacy_over_tapes(int r, int L, int neighborhood_len,
                                        const std::vector<char>& rule_bits,
                                        const std::array<int,8>& perm,
                                        std::ostream& logf) {
    if (L <= 0 || L >= 63) return false;
    unsigned long long words = 1ULL << L;
    std::size_t ti = 0;
    for (unsigned long long mask = 0; mask < words; ++mask) {
        std::string w(L, '0');
        for (int i = 0; i < L; ++i) {
            unsigned long long bit = 1ULL << (L - 1 - i);
            if (mask & bit) w[i] = '1';
        }
        for (int pos = 0; pos < L; ++pos) {
            for (int qi = 0; qi < 8; ++qi) {
                const std::string& q = STATE_LABELS[qi];
                std::string wH;
                int posH;
                std::string qH;
                if (!apply_H_TMT(w, pos, q, r, neighborhood_len,
                                  rule_bits, perm, wH, posH, qH)) {
                    logf << "x#" << ti << " H indefinida\n";
                    return false;
                }
                RunResult resT = run_original(1, wH, posH, qH);
                if (!resT.ok) {
                    logf << "x#" << ti << " T fallo\n";
                    return false;
                }
                std::string wTH = resT.word_out;
                int         posTH = (int)resT.pos_out;
                std::string qTH = resT.state_out;
                std::string wHTH;
                int posHTH;
                std::string qHTH;
                if (!apply_H_TMT(wTH, posTH, qTH, r, neighborhood_len,
                                  rule_bits, perm, wHTH, posHTH, qHTH)) {
                    logf << "x#" << ti << " H en T(H(x)) indefinida\n";
                    return false;
                }
                RunResult resInv = run_inversa(1, w, pos, q);
                if (!resInv.ok) {
                    logf << "x#" << ti << " T^-1 fallo\n";
                    return false;
                }
                std::string wInv = resInv.word_out;
                int         posInv = (int)resInv.pos_out;
                std::string qInv = resInv.state_out;
                if (!(wHTH == wInv && posHTH == posInv && qHTH == qInv)) {
                    logf << "x#" << ti << " no cumple T^-1 = H∘T∘H\n";
                    logf << "x     = (" << w << ";" << pos << ";" << q << ")\n";
                    logf << "Hx    = (" << wH << ";" << posH << ";" << qH << ")\n";
                    logf << "THx   = (" << wTH << ";" << posTH << ";" << qTH << ")\n";
                    logf << "HTHx  = (" << wHTH << ";" << posHTH << ";" << qHTH << ")\n";
                    logf << "Tinvx = (" << wInv << ";" << posInv << ";" << qInv << ")\n";
                    return false;
                }
                if (ti < 10) {
                    logf << "x#" << ti << " ok formula | x=("
                         << w << ";" << pos << ";" << q << ")\n";
                }
                ++ti;
            }
        }
    }
    return true;
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
    long long progress_interval = 100000;  // también usado como intervalo de log
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--logdir" && i + 1 < argc) {
            logdir = argv[++i];
        } else if (arg == "--progress-interval" && i + 1 < argc) {
            progress_interval = std::stoll(argv[++i]);
        }
    }

    std::filesystem::create_directories(logdir);
    long long inv_count = count_involutive_perms_8();
    std::vector<std::array<int,8>> perms = generate_involutive_permutations_8();

    std::atomic<bool> found(false);
    std::string found_path;
    int found_r = -1;
    std::mutex io_mutex;

    int r = 1;
    while (true) {
        int d = 2 * r;
        int L = 2 * d + 1;
        std::filesystem::path rdir =
            std::filesystem::path(logdir) / ("r" + std::to_string(r));
        std::filesystem::create_directories(rdir);

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

            std::atomic<std::size_t> next_perm(0);
            unsigned int thread_count = std::thread::hardware_concurrency();
            if (thread_count == 0) thread_count = 1;
            std::vector<std::thread> threads;
            threads.reserve(thread_count);

            for (unsigned int t = 0; t < thread_count; ++t) {
                threads.emplace_back([&, base_idx]() {
                    int neighborhood_len = K;
                    NullBuffer nbuf;
                    std::ostream devnull(&nbuf);

                    while (true) {
                        if (found.load()) return;

                        std::size_t p_idx = next_perm.fetch_add(1);
                        if (p_idx >= perms.size()) return;

                        long long h_idx = base_idx + static_cast<long long>(p_idx) + 1;
                        long long tnum = tested.fetch_add(1) + 1;

                        if (progress_interval > 0 && tnum % progress_interval == 0) {
                            std::lock_guard<std::mutex> lock(io_mutex);
                            std::cout << "r=" << r << " progreso: "
                                      << tnum << " de "
                                      << static_cast<long double>(total_H) << "\n";
                            std::cout.flush();
                        }

                        bool log_this =
                            (progress_interval > 0 && (tnum % progress_interval == 0));

                        std::filesystem::path fpath;
                        std::ofstream f;
                        std::ostream* logp = &devnull;

                        if (log_this) {
                            fpath = rdir / ("H_" + std::to_string(h_idx) + ".log");
                            f.open(fpath);
                            if (f) {
                                f << fmt_rule_bits_table(rule_bits, r, neighborhood_len)
                                  << "\n";
                                f << fmt_perm(perms[p_idx]) << "\n";
                                logp = &f;
                            } else {
                                log_this = false;
                                logp = &devnull;
                            }
                        }

                        if (!verify_involution_over_tapes(r, L, neighborhood_len,
                                                          rule_bits, perms[p_idx],
                                                          *logp)) {
                            continue;
                        }

                        bool ok = verify_conjugacy_over_tapes(r, L, neighborhood_len,
                                                              rule_bits, perms[p_idx],
                                                              *logp);
                        if (!ok) continue;

                        bool expected = false;
                        if (found.compare_exchange_strong(expected, true)) {
                            // Este hilo es el primero que encuentra un H válido.
                            if (!log_this) {
                                fpath = rdir / ("H_" + std::to_string(h_idx) + ".log");
                                std::ofstream fout(fpath);
                                if (fout) {
                                    fout << fmt_rule_bits_table(rule_bits, r, neighborhood_len)
                                         << "\n";
                                    fout << fmt_perm(perms[p_idx]) << "\n";
                                    verify_involution_over_tapes(r, L, neighborhood_len,
                                                                 rule_bits, perms[p_idx],
                                                                 fout);
                                    verify_conjugacy_over_tapes(r, L, neighborhood_len,
                                                                rule_bits, perms[p_idx],
                                                                fout);
                                    fout << "ENCONTRADA\n";
                                    fout.flush();
                                }
                            } else {
                                f << "ENCONTRADA\n";
                                f.flush();
                            }

                            {
                                std::lock_guard<std::mutex> lock(io_mutex);
                                found_path = fpath.string();
                                found_r = r;
                                std::cout << "H encontrada en r=" << r
                                          << ", archivo=" << found_path << "\n";
                                std::cout.flush();
                            }
                        }

                        return;  // este hilo ya no necesita seguir
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
