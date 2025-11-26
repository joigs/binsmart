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

using namespace std;

struct NullBuffer : public std::streambuf {
    int overflow(int c) override { return c; }
};

// =======================  CA / H  =======================

static bool apply_symbol_CA(const string& word, int r, int neighborhood_len,
                            const vector<char>& rule_bits, string& out) {
    int L = (int)word.size();
    out.clear();
    out.reserve(L);
    int K = neighborhood_len;
    int S = (int)rule_bits.size();
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

static bool apply_H_TMT(const string& word, int pos, const string& qlbl,
                        int r, int neighborhood_len, const vector<char>& rule_bits,
                        const array<int,8>& perm,
                        string& w2, int& pos2, string& q2) {
    if (!apply_symbol_CA(word, r, neighborhood_len, rule_bits, w2)) return false;
    int qi = state_index_from_label(qlbl);
    if (qi < 0) return false;
    int qnext = perm[qi];
    pos2 = pos;
    q2 = STATE_LABELS[qnext];
    return true;
}

static string fmt_rule_bits_table(const vector<char>& rule_bits,
                                  int r, int neighborhood_len) {
    ostringstream oss;
    oss << "SIMBOLOS r=" << r << "\n";
    int S = (int)rule_bits.size();
    int K = neighborhood_len;
    for (int idx = 0; idx < S; ++idx) {
        string key(K, '0');
        for (int b = 0; b < K; ++b) {
            int bitpos = K - 1 - b;
            char c = (idx & (1 << bitpos)) ? '1' : '0';
            key[b] = c;
        }
        string left, center, right;
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

static string fmt_perm(const array<int,8>& perm) {
    ostringstream oss;
    oss << "ESTADOS sigma (involucion)\n";
    for (int i = 0; i < 8; ++i) {
        oss << "  " << STATE_LABELS[i] << " -> " << STATE_LABELS[perm[i]] << "\n";
    }
    return oss.str();
}

// =======================  VERIFICACIONES  =======================

// H∘H: opcionalmente escribe unas pocas muestras si logf!=nullptr
static bool verify_involution_over_tapes(int r, int L, int neighborhood_len,
                                         const vector<char>& rule_bits,
                                         const array<int,8>& perm,
                                         ostream* logf) {
    if (L <= 0 || L >= 63) return false;

    bool do_log = (logf != nullptr);
    const size_t MAX_OK_LOG = 100;
    unsigned long long stride = 1ULL;
    size_t ok_logged = 0;
    if (do_log) {
        unsigned long long words = 1ULL << L;
        unsigned long long total_x = words * (unsigned long long)L * 8ULL;
        if (MAX_OK_LOG > 0 && total_x > MAX_OK_LOG) {
            stride = total_x / MAX_OK_LOG;
        }
    }

    unsigned long long ti = 0;  // índice global de configuración

    unsigned long long words = 1ULL << L;
    string w(L, '0'), w1, w2;

    for (unsigned long long mask = 0; mask < words; ++mask) {
        // reconstruir palabra según mask
        for (int i = 0; i < L; ++i) {
            unsigned long long bit = 1ULL << (L - 1 - i);
            w[i] = (mask & bit) ? '1' : '0';
        }

        for (int pos = 0; pos < L; ++pos) {
            for (int qi = 0; qi < 8; ++qi) {
                const string& q = STATE_LABELS[qi];

                int pos1, pos2;
                string q1, q2;

                if (!apply_H_TMT(w, pos, q, r, neighborhood_len,
                                  rule_bits, perm, w1, pos1, q1)) {
                    if (do_log) {
                        (*logf) << "x#" << ti << " H indefinida | x=("
                                << w << "; head=" << pos << "; state=" << q << ")\n";
                    }
                    return false;
                }

                if (!apply_H_TMT(w1, pos1, q1, r, neighborhood_len,
                                  rule_bits, perm, w2, pos2, q2)) {
                    if (do_log) {
                        (*logf) << "x#" << ti << " H∘H indefinida | x=("
                                << w << "; head=" << pos << "; state=" << q
                                << ") | Hx=(" << w1 << "; " << pos1 << "; " << q1 << ")\n";
                    }
                    return false;
                }

                if (!(w2 == w && pos2 == pos && q2 == q)) {
                    if (do_log) {
                        (*logf) << "x#" << ti << " H∘H(x) != x\n";
                        (*logf) << "x    = (" << w << "; head=" << pos << "; state=" << q << ")\n";
                        (*logf) << "Hx   = (" << w1 << "; head=" << pos1 << "; state=" << q1 << ")\n";
                        (*logf) << "HHx  = (" << w2 << "; head=" << pos2 << "; state=" << q2 << ")\n";
                    }
                    return false;
                }

                if (do_log && ok_logged < MAX_OK_LOG && (ti % stride == 0)) {
                    (*logf) << "x#" << ti << " ok H∘H | x=("
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

// Fórmula T^{-1} = H∘T∘H, opcionalmente con algunas muestras si logf!=nullptr
static bool verify_conjugacy_over_tapes(int r, int L, int neighborhood_len,
                                        const vector<char>& rule_bits,
                                        const array<int,8>& perm,
                                        ostream* logf) {
    if (L <= 0 || L >= 63) return false;

    bool do_log = (logf != nullptr);
    const size_t MAX_OK_LOG = 64;
    unsigned long long stride = 1ULL;
    size_t ok_logged = 0;
    if (do_log) {
        unsigned long long words = 1ULL << L;
        unsigned long long total_x = words * (unsigned long long)L * 8ULL;
        if (MAX_OK_LOG > 0 && total_x > MAX_OK_LOG) {
            stride = total_x / MAX_OK_LOG;
        }
    }

    unsigned long long ti = 0;
    unsigned long long words = 1ULL << L;
    string w(L, '0'), wH, wTH, wHTH, wInv;

    for (unsigned long long mask = 0; mask < words; ++mask) {
        // reconstruir palabra
        for (int i = 0; i < L; ++i) {
            unsigned long long bit = 1ULL << (L - 1 - i);
            w[i] = (mask & bit) ? '1' : '0';
        }

        for (int pos = 0; pos < L; ++pos) {
            for (int qi = 0; qi < 8; ++qi) {
                const string& q = STATE_LABELS[qi];

                int posH, posTH, posHTH, posInv;
                string qH, qTH, qHTH, qInv;

                if (!apply_H_TMT(w, pos, q, r, neighborhood_len,
                                  rule_bits, perm, wH, posH, qH)) {
                    if (do_log) (*logf) << "x#" << ti << " H indefinida\n";
                    return false;
                }

                RunResult resT = run_original(1, wH, posH, qH);
                if (!resT.ok) {
                    if (do_log) (*logf) << "x#" << ti << " T fallo\n";
                    return false;
                }
                wTH   = resT.word_out;
                posTH = (int)resT.pos_out;
                qTH   = resT.state_out;

                if (!apply_H_TMT(wTH, posTH, qTH, r, neighborhood_len,
                                  rule_bits, perm, wHTH, posHTH, qHTH)) {
                    if (do_log) (*logf) << "x#" << ti << " H en T(H(x)) indefinida\n";
                    return false;
                }

                RunResult resInv = run_inversa(1, w, pos, q);
                if (!resInv.ok) {
                    if (do_log) (*logf) << "x#" << ti << " T^-1 fallo\n";
                    return false;
                }
                wInv   = resInv.word_out;
                posInv = (int)resInv.pos_out;
                qInv   = resInv.state_out;

                if (!(wHTH == wInv && posHTH == posInv && qHTH == qInv)) {
                    if (do_log) {
                        (*logf) << "x#" << ti << " no cumple T^-1 = H∘T∘H\n";
                        (*logf) << "x     = (" << w << ";" << pos << ";" << q << ")\n";
                        (*logf) << "Hx    = (" << wH << ";" << posH << ";" << qH << ")\n";
                        (*logf) << "THx   = (" << wTH << ";" << posTH << ";" << qTH << ")\n";
                        (*logf) << "HTHx  = (" << wHTH << ";" << posHTH << ";" << qHTH << ")\n";
                        (*logf) << "Tinvx = (" << wInv << ";" << posInv << ";" << qInv << ")\n";
                    }
                    return false;
                }

                if (do_log && ok_logged < MAX_OK_LOG && (ti % stride == 0)) {
                    (*logf) << "x#" << ti << " ok formula | x=("
                            << w << ";" << pos << ";" << q << ")\n";
                    ++ok_logged;
                }

                ++ti;
            }
        }
    }

    return true;
}

// =======================  PERMUTACIONES INVOLUTIVAS  =======================

static void involutive_permutations_dfs(int n,
                                        vector<bool>& used,
                                        array<int,8>& p,
                                        int i,
                                        vector<array<int,8>>& out) {
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

static vector<array<int,8>> generate_involutive_permutations_8() {
    int n = 8;
    vector<array<int,8>> out;
    vector<bool> used(n, false);
    array<int,8> p;
    for (int i = 0; i < n; ++i) p[i] = -1;
    involutive_permutations_dfs(n, used, p, 0, out);
    return out;
}

static long long count_involutive_perms_8() {
    int n = 8;
    vector<long long> fact(n + 1);
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

// combinaciones simples (sin recursión pesada)
template<typename F>
static void for_each_combination(int n, int k, F f) {
    if (k < 0 || k > n) return;
    if (k == 0) {
        vector<int> empty;
        f(empty);
        return;
    }
    vector<int> comb(k);
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

// =======================  MAIN  =======================

int main(int argc, char** argv) {
    string logdir = "logs_tmt";
    long long progress_interval = 100000;
    unsigned int threads_param = 0;   // 0 => usar hardware_concurrency

    for (int i = 1; i < argc; ++i) {
        string arg = argv[i];
        if (arg == "--logdir" && i + 1 < argc) {
            logdir = argv[++i];
        } else if (arg == "--progress-interval" && i + 1 < argc) {
            progress_interval = stoll(argv[++i]);
        } else if (arg == "--threads" && i + 1 < argc) {
            threads_param = (unsigned int)stoul(argv[++i]);
        }
    }

    filesystem::create_directories(logdir);
    long long inv_count = count_involutive_perms_8();
    vector<array<int,8>> perms = generate_involutive_permutations_8();

    atomic<bool> found(false);
    string found_path;
    int found_r = -1;
    mutex io_mutex;

    unsigned int base_thread_count = threads_param ? threads_param
                                                   : thread::hardware_concurrency();
    if (base_thread_count == 0) base_thread_count = 1;

    {
        lock_guard<mutex> lock(io_mutex);
        cout << "Usando " << base_thread_count << " hilos de trabajo\n";
        cout.flush();
    }

    int r = 1;
    while (true) {
        int d = 2 * r;
        int L = 2 * d + 1;
        filesystem::path rdir =
            filesystem::path(logdir) / ("r" + to_string(r));
        filesystem::create_directories(rdir);

        int K = 2 * r + 1;
        int S = 1 << K;

        long double num_sym_bal = 0.0L;
        if (S % 2 == 0) {
            int half = S / 2;
            long double c = 1.0L;
            for (int i = 1; i <= half; ++i) {
                c *= (long double)(S + 1 - i);
                c /= (long double)i;
            }
            num_sym_bal = c;
        }
        long double total_H = num_sym_bal * (long double)inv_count;

        {
            lock_guard<mutex> lock(io_mutex);
            cout << "Iniciando r=" << r
                 << ", L=" << L
                 << ", H_balanceadas_max=" << (long double)total_H
                 << "\n";
            cout.flush();
        }

        atomic<long long> tested(0);
        long long sym_rule_idx = 0;
        int half = S / 2;

        for_each_combination(S, half, [&](const vector<int>& ones) {
            if (found.load()) return;

            vector<char> rule_bits(S, '0');
            for (int idx : ones) rule_bits[idx] = '1';

            long long base_idx = sym_rule_idx * inv_count;
            sym_rule_idx++;

            atomic<size_t> next_perm(0);
            unsigned int thread_count = base_thread_count;
            vector<thread> threads;
            threads.reserve(thread_count);

            for (unsigned int t = 0; t < thread_count; ++t) {
                threads.emplace_back([&, base_idx]() {
                    int neighborhood_len = K;

                    while (true) {
                        if (found.load()) return;

                        size_t p_idx = next_perm.fetch_add(1);
                        if (p_idx >= perms.size()) return;

                        long long h_idx = base_idx + (long long)p_idx + 1;
                        long long tnum = tested.fetch_add(1) + 1;

                        if (progress_interval > 0 &&
                            tnum % progress_interval == 0) {
                            lock_guard<mutex> lock(io_mutex);
                            cout << "r=" << r << " progreso: "
                                 << tnum << " de "
                                 << (long double)total_H << "\n";
                            cout.flush();
                        }

                        // Primero solo comprobamos sin log (rápido)
                        if (!verify_involution_over_tapes(
                                r, L, neighborhood_len, rule_bits, perms[p_idx],
                                nullptr)) {
                            continue;
                        }

                        if (!verify_conjugacy_over_tapes(
                                r, L, neighborhood_len, rule_bits, perms[p_idx],
                                nullptr)) {
                            continue;
                        }

                        // Aquí H es bueno: intentamos registrar y detener
                        bool expected = false;
                        if (!found.compare_exchange_strong(expected, true)) {
                            // Otro hilo ya encontró uno; salimos
                            return;
                        }

                        // Solo el primer hilo que entra aquí escribe el log final
                        filesystem::path fpath =
                            rdir / ("H_" + to_string(h_idx) + ".log");
                        ofstream logf(fpath);
                        if (logf) {
                            logf << fmt_rule_bits_table(rule_bits, r, neighborhood_len)
                                 << "\n";
                            logf << fmt_perm(perms[p_idx]) << "\n";
                            verify_involution_over_tapes(
                                r, L, neighborhood_len, rule_bits, perms[p_idx],
                                &logf);
                            verify_conjugacy_over_tapes(
                                r, L, neighborhood_len, rule_bits, perms[p_idx],
                                &logf);
                            logf << "ENCONTRADA\n";
                            logf.flush();
                        }

                        {
                            lock_guard<mutex> lock(io_mutex);
                            found_path = fpath.string();
                            found_r = r;
                            cout << "H encontrada en r=" << r
                                 << ", archivo=" << found_path << "\n";
                            cout.flush();
                        }

                        return; // este hilo ya no necesita seguir
                    }
                });
            }

            for (auto& th : threads) th.join();
        });

        if (found.load()) break;

        {
            lock_guard<mutex> lock(io_mutex);
            cout << "Terminado r=" << r << " sin encontrar H\n";
            cout.flush();
        }

        r += 1;
    }

    return 0;
}
